import A12Kernel.Elaboration.AddressedNumberAbs

/-! # Addressed Number `Abs` locks

The matrix separates exact-scale admission, negative and already-positive values, empty zero, row-local poison, target rejection, source-relative classification, and exact addresses.
-/

namespace A12Kernel.Conformance.AddressedNumberAbs

open A12Kernel

private def source : FlatFieldDecl := {
  id := 1
  groupPath := ["Order", "Rows"]
  name := "Source"
  policy := { kind := .number { scale := 2, signed := true } }
  repeatableScope := [10]
}

private def target : FlatFieldDecl := {
  source with
    id := 2
    name := "Target"
    numericTargetConstraints := { maximum := some (999 / 100) }
}

private def wrong : FlatFieldDecl := {
  source with id := 3, name := "Wrong", policy := { kind := .string }
}

private def outer : FlatFieldDecl := {
  source with id := 4, name := "Outer", groupPath := ["Order"], repeatableScope := []
}

private def scaleZero : FlatFieldDecl := {
  target with
    id := 5
    name := "ScaleZero"
    policy := { kind := .number { scale := 0, signed := true } }
    numericTargetConstraints := {}
}

private def model : FlatModel := {
  fields := [source, target, wrong, outer, scaleZero]
  repeatableGroups := [{ level := 10, path := ["Order", "Rows"], repeatability := some 5 }]
}

private def prepared : PreparedFlatStringContext model builtinStringPatternCompiler :=
  (prepareFlatStringContext { now := { epochMillis := 0 } }
    builtinStringPatternCompiler model).toOption.get (by native_decide)

private def bare (field : String) : SurfaceFieldPath :=
  { base := .relative 0, groups := [], field }

private def parent (field : String) : SurfaceFieldPath :=
  { base := .relative 1, groups := [], field }

private def operation? : Option (CheckedAddressedNumberAbs model) :=
  (checkAddressedNumberAbs model ["Order", "Rows"] target.id
    (bare "Source")).toOption

private def cell (field : FieldId) (row : Nat)
    (stored : String) (raw : RawCell) : ClassifiedCellInput :=
  { address := { field, path := [row] }, stored, raw }

private def decimalCell (field : FieldId) (row : Nat) (stored : String)
    (unscaled scale : Int) (raw : RawCell) : ClassifiedCellInput := {
  address := { field, path := [row] }
  stored
  raw
  numericDecimal := some { unscaled, scale }
}

private def input? (cells : List ClassifiedCellInput) :
    Option (CheckedDocument model) :=
  (checkDocument prepared "en_US" {
    instantiatedRows := (List.range 5).map fun i => { group := 10, path := [i + 1] }
    cells
  }).toOption

private def outcomes? (cells : List ClassifiedCellInput) :
    Option (List (SourcedNumericTargetOutcome CellAddr)) := do
  let operation ← operation?
  let input ← input? cells
  (operation.execute input).toOption

private def result? (cells : List ClassifiedCellInput) :
    Option (NumericComputationRunView
      (ComputationFormalMessage Unit) CellAddr) := do
  let operation ← operation?
  let input ← input? cells
  (operation.executeResult input (fun _ => ()) []).toOption

private def addr (field : FieldId) (row : Nat) : CellAddr :=
  { field, path := [row] }

private def stored (unscaled : Int) (scale : Nat) : StoredNumber :=
  { unscaled, scale }

/- `Abs` shares the direct Number source certificate: one Number source and an exact target/source scale. -/
example :
    operation?.isSome = true ∧
    (match checkAddressedNumberAbs model ["Order", "Rows"] target.id (bare "Wrong") with
      | .error (.sourceNotNumber path .string) => path == wrong.path
      | _ => false) = true ∧
    (match checkAddressedNumberAbs model ["Order", "Rows"] scaleZero.id (bare "Source") with
      | .error (.scaleMismatch 0 2) => true
      | _ => false) = true ∧
    (checkAddressedNumberAbs model ["Order", "Rows"] target.id
      (parent "Outer")).isOk = true := by
  native_decide

/- Absolute value transforms the signed source exactly once while retaining empty zero, poison, target rejection, and row keys. -/
example :
    (outcomes? [
      cell source.id 2 "-5.25" (.parsed (.num (-21 / 4))),
      cell source.id 3 "3.50" (.parsed (.num (7 / 2))),
      cell source.id 4 "bad" (.rejected .malformed),
      cell source.id 5 "-12.34" (.parsed (.num (-617 / 50)))
    ]).map (·.map fun entry => (entry.targetField, entry.outcome)) =
      some [
        (addr target.id 1, .accepted (stored 0 0)),
        (addr target.id 2, .accepted (stored 525 2)),
        (addr target.id 3, .accepted (stored 35 1)),
        (addr target.id 4, .inheritedPoison .malformed),
        (addr target.id 5, .rejected (stored 1234 2) .aboveMaximum)
      ] := by
  native_decide

/- Source-relative classification keeps the equal-magnitude negative row unchanged and exposes every other public branch at its exact address. -/
example :
    (do
      let view ← result? [
        cell source.id 2 "-5.25" (.parsed (.num (-21 / 4))),
        decimalCell target.id 2 "5.25" 525 2 (.parsed (.num (21 / 4))),
        cell source.id 3 "3.50" (.parsed (.num (7 / 2))),
        decimalCell target.id 3 "1.00" 100 2 (.parsed (.num 1)),
        cell source.id 4 "bad" (.rejected .malformed),
        cell target.id 4 "7.00" (.parsed (.num 7)),
        cell source.id 5 "-12.34" (.parsed (.num (-617 / 50)))
      ]
      pure (
        view.withoutErrors,
        view.withChanges,
        view.cleared,
        view.withErrors)) =
      some (
        [
          { targetField := addr target.id 1, value := stored 0 0 },
          { targetField := addr target.id 2, value := stored 525 2 },
          { targetField := addr target.id 3, value := stored 35 1 }
        ],
        [
          { targetField := addr target.id 1, value := stored 0 0 },
          { targetField := addr target.id 3, value := stored 35 1 }
        ],
        [addr target.id 4],
        [{
          targetField := addr target.id 5
          attempted := stored 1234 2
          cause := .aboveMaximum
        }]) := by
  native_decide

end A12Kernel.Conformance.AddressedNumberAbs
