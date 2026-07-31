import A12Kernel.Elaboration.AddressedNumberRound

/-! # Addressed direct-Number rounding locks

The matrix separates floor, ceiling, and half-up direction, omitted and explicit result scales, empty zero, poison, target rejection, source-relative classification, and exact addresses.
-/

namespace A12Kernel.Conformance.AddressedNumberRound

open A12Kernel

private def source : FlatFieldDecl := {
  id := 1
  groupPath := ["Cart", "Lines"]
  name := "Source"
  policy := { kind := .number { scale := 3, signed := true } }
  repeatableScope := [10]
}

private def target (id : FieldId) (name : String) (scale : Nat)
    (maximum : Rat) : FlatFieldDecl := {
  source with
    id
    name
    policy := { kind := .number { scale, signed := true } }
    numericTargetConstraints := { maximum := some maximum }
}

private def down := target 2 "Down" 0 9
private def up := target 3 "Up" 1 (99 / 10)
private def accounting := target 4 "Accounting" 0 9

private def model : FlatModel := {
  fields := [source, down, up, accounting]
  repeatableGroups := [{ level := 10, path := ["Cart", "Lines"], repeatability := some 6 }]
}

private def prepared : PreparedFlatStringContext model builtinStringPatternCompiler :=
  (prepareFlatStringContext { now := { epochMillis := 0 } }
    builtinStringPatternCompiler model).toOption.get (by native_decide)

private def places0 : RoundingPlaces := ⟨0, by decide⟩
private def places1 : RoundingPlaces := ⟨1, by decide⟩

private def sourceRef : SurfaceFieldPath :=
  { base := .relative 0, groups := [], field := "Source" }

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

private def sourceCells : List ClassifiedCellInput := [
  cell source.id 1 "-1.450" (.parsed (.num (-29 / 20))),
  cell source.id 2 "-2.500" (.parsed (.num (-5 / 2))),
  cell source.id 3 "1.250" (.parsed (.num (5 / 4))),
  cell source.id 5 "bad" (.rejected .malformed),
  cell source.id 6 "12.345" (.parsed (.num (2469 / 200)))
]

private def input? (extra : List ClassifiedCellInput := []) :
    Option (CheckedDocument model) :=
  (checkDocument prepared "en_US" {
    instantiatedRows := (List.range 6).map fun i => { group := 10, path := [i + 1] }
    cells := sourceCells ++ extra
  }).toOption

private def operation? (target : FlatFieldDecl)
    (mode : DecimalRoundingMode) (places : RoundingPlaces) :
    Option (CheckedAddressedNumberRound model) :=
  (checkAddressedNumberRound model ["Cart", "Lines"] target.id sourceRef
    mode places).toOption

private def outcomes? (target : FlatFieldDecl)
    (mode : DecimalRoundingMode) (places : RoundingPlaces) :
    Option (List (CellAddr × NumericTargetOutcome)) := do
  let operation ← operation? target mode places
  let input ← input?
  let outcomes ← (operation.execute input).toOption
  pure (outcomes.map fun entry => (entry.targetField, entry.outcome))

private def result? (extra : List ClassifiedCellInput) :
    Option (NumericComputationRunView
      (ComputationFormalMessage Unit) CellAddr) := do
  let operation ← operation? down .floor places0
  let input ← input? extra
  (operation.executeResult input (fun _ => ()) []).toOption

private def addr (field : FieldId) (row : Nat) : CellAddr :=
  { field, path := [row] }

private def stored (unscaled : Int) (scale : Nat) : StoredNumber :=
  { unscaled, scale }

example :
    (operation? down .floor places0).isSome = true ∧
    (operation? up .ceiling places1).isSome = true ∧
    (operation? accounting .halfUp places0).isSome = true ∧
    (match checkAddressedNumberRound model ["Cart", "Lines"] down.id
        sourceRef .ceiling places1 with
      | .error (.scaleMismatch 0 1) => true
      | _ => false) = true := by
  native_decide

example : outcomes? down .floor places0 = some [
    (addr down.id 1, .accepted (stored (-2) 0)),
    (addr down.id 2, .accepted (stored (-3) 0)),
    (addr down.id 3, .accepted (stored 1 0)),
    (addr down.id 4, .accepted (stored 0 0)),
    (addr down.id 5, .inheritedPoison .malformed),
    (addr down.id 6, .rejected (stored 12 0) .aboveMaximum)
  ] := by native_decide

example : outcomes? up .ceiling places1 = some [
    (addr up.id 1, .accepted (stored (-14) 1)),
    (addr up.id 2, .accepted (stored (-25) 1)),
    (addr up.id 3, .accepted (stored 13 1)),
    (addr up.id 4, .accepted (stored 0 0)),
    (addr up.id 5, .inheritedPoison .malformed),
    (addr up.id 6, .rejected (stored 124 1) .aboveMaximum)
  ] := by native_decide

example : outcomes? accounting .halfUp places0 = some [
    (addr accounting.id 1, .accepted (stored (-1) 0)),
    (addr accounting.id 2, .accepted (stored (-3) 0)),
    (addr accounting.id 3, .accepted (stored 1 0)),
    (addr accounting.id 4, .accepted (stored 0 0)),
    (addr accounting.id 5, .inheritedPoison .malformed),
    (addr accounting.id 6, .rejected (stored 12 0) .aboveMaximum)
  ] := by native_decide

example :
    (do
      let view ← result? [
        decimalCell down.id 1 "-2" (-2) 0 (.parsed (.num (-2))),
        cell down.id 2 "0" (.parsed (.num 0)),
        cell down.id 5 "7" (.parsed (.num 7))
      ]
      pure (view.withChanges.map (·.targetField), view.cleared,
        view.withErrors.map (·.targetField))) =
      some (
        [addr down.id 2, addr down.id 3, addr down.id 4],
        [addr down.id 5],
        [addr down.id 6]) := by
  native_decide

end A12Kernel.Conformance.AddressedNumberRound
