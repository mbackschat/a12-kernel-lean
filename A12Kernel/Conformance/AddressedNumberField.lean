import A12Kernel.Elaboration.AddressedNumberField

/-! # Addressed direct Number-field locks

The matrix separates exact-scale admission, empty zero, row-local value and poison, target rejection, source-relative result classification, and exact addresses.
-/

namespace A12Kernel.Conformance.AddressedNumberField

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
  repeatableGroups := [{ level := 10, path := ["Order", "Rows"], repeatability := some 4 }]
}

private def prepared : PreparedFlatStringContext model builtinStringPatternCompiler :=
  (prepareFlatStringContext { now := { epochMillis := 0 } }
    builtinStringPatternCompiler model).toOption.get (by native_decide)

private def bare (field : String) : SurfaceFieldPath :=
  { base := .relative 0, groups := [], field }

private def parent (field : String) : SurfaceFieldPath :=
  { base := .relative 1, groups := [], field }

private def operation? : Option (CheckedAddressedNumberField model) :=
  (checkAddressedNumberField model ["Order", "Rows"] target.id
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
    instantiatedRows := (List.range 4).map fun i => { group := 10, path := [i + 1] }
    cells
  }).toOption

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

/- Exact source and target scales are part of checked authoring; wrong kind and scope fail separately. -/
example :
    operation?.isSome = true ∧
    (match checkAddressedNumberField model ["Order", "Rows"] target.id (bare "Wrong") with
      | .error (.sourceNotNumber path .string) => path == wrong.path
      | _ => false) = true ∧
    (match checkAddressedNumberField model ["Order", "Rows"] scaleZero.id (bare "Source") with
      | .error (.scaleMismatch 0 2) => true
      | _ => false) = true ∧
    (match checkAddressedNumberField model ["Order", "Rows"] target.id (parent "Outer") with
      | .error (.placement (.scopeMismatch targetPath sourcePath)) =>
          targetPath == target.path && sourcePath == outer.path
      | _ => false) = true := by
  native_decide

/- The direct read retains empty-as-zero, exact row values, formal poison, target rejection, and source-relative change identity. -/
example :
    (do
      let view ← result? [
        cell source.id 2 "1.25" (.parsed (.num (5 / 4))),
        decimalCell target.id 2 "1.25" 125 2 (.parsed (.num (5 / 4))),
        cell source.id 3 "bad" (.rejected .malformed),
        cell target.id 3 "2.00" (.parsed (.num 2)),
        cell source.id 4 "12.34" (.parsed (.num (617 / 50)))
      ]
      pure (view.withChanges.map fun entry => (entry.targetField, entry.value),
        view.cleared, view.withErrors)) =
      some (
        [(addr target.id 1, stored 0 0)],
        [addr target.id 3],
        [{
          targetField := addr target.id 4
          attempted := stored 1234 2
          cause := .aboveMaximum
        }]) := by
  native_decide

end A12Kernel.Conformance.AddressedNumberField
