import A12Kernel.Elaboration.AddressedNumberExtremum

/-! # Same-scope repeatable direct-Number extrema locks -/

namespace A12Kernel.Conformance.AddressedNumberExtremum

open A12Kernel

private def number (id : FieldId) (name : String) (scale : Nat) : FlatFieldDecl := {
  id
  groupPath := ["Probe", "Rows"]
  name
  policy := { kind := .number { scale, signed := true } }
  repeatableScope := [10]
}

private def left := number 1 "A" 0
private def right : FlatFieldDecl := {
  number 2 "B" 2 with
  numericTargetConstraints := { maximum := some 10 }
}
private def minimum : FlatFieldDecl := {
  number 3 "Minimum" 2 with
  numericTargetConstraints := { minimum := some (-999 / 100) }
}
private def maximum : FlatFieldDecl := {
  number 4 "Maximum" 2 with
  numericTargetConstraints := { maximum := some (999 / 100) }
}
private def wrongScale := number 5 "WrongScale" 0

private def model : FlatModel := {
  fields := [left, right, minimum, maximum, wrongScale]
  repeatableGroups := [{
    level := 10
    path := ["Probe", "Rows"]
    repeatability := some 7
  }]
}

private def prepared : PreparedFlatStringContext model builtinStringPatternCompiler :=
  (prepareFlatStringContext { now := { epochMillis := 0 } }
    builtinStringPatternCompiler model).toOption.get (by native_decide)

private def bare (field : String) : SurfaceFieldPath :=
  { base := .relative 0, groups := [], field }

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

private def inputResult (extra : List ClassifiedCellInput := []) :=
  checkDocument prepared "en_US" {
    instantiatedRows := (List.range 7).map fun i =>
      { group := 10, path := [i + 1] }
    cells := [
      cell left.id 1 "3" (.parsed (.num 3)),
      cell right.id 1 "5.25" (.parsed (.num (21 / 4))),
      cell right.id 2 "5.25" (.parsed (.num (21 / 4))),
      cell left.id 3 "-2" (.parsed (.num (-2))),
      cell left.id 5 "bad-left" (.rejected .malformed),
      cell right.id 5 "12" (.rejected .declaredConstraint),
      cell left.id 6 "4" (.parsed (.num 4)),
      cell right.id 6 "12" (.rejected .declaredConstraint),
      cell left.id 7 "12" (.parsed (.num 12)),
      cell right.id 7 "4" (.parsed (.num 4))
    ] ++ extra
  }

private def input? (extra : List ClassifiedCellInput := []) :
    Option (CheckedDocument model) := (inputResult extra).toOption

private def operation? (target : FlatFieldDecl) (op : NumericExtremumOp) :
    Option (CheckedAddressedNumberExtremum model) :=
  (checkAddressedNumberExtremum model ["Probe", "Rows"] target.id
    (bare "A") (bare "B") op).toOption

private def addr (field : FieldId) (row : Nat) : CellAddr :=
  { field, path := [row] }

private def stored (unscaled : Int) (scale : Nat) : StoredNumber :=
  { unscaled, scale }

private def outcomes? (target : FlatFieldDecl) (op : NumericExtremumOp) :
    Option (List (CellAddr × NumericTargetOutcome)) := do
  let operation ← operation? target op
  let input ← input?
  let outcomes ← (operation.execute input).toOption
  pure (outcomes.map fun entry => (entry.targetField, entry.outcome))

private def result? (extra : List ClassifiedCellInput) :
    Option (NumericComputationRunView
      (ComputationFormalMessage Unit) CellAddr) := do
  let operation ← operation? maximum .maximum
  let input ← input? extra
  (operation.executeResult input (fun _ => ()) []).toOption

example :
    (operation? minimum .minimum).isSome = true ∧
    (operation? maximum .maximum).isSome = true ∧
    (match checkAddressedNumberExtremum model ["Probe", "Rows"]
        wrongScale.id (bare "A") (bare "B") .minimum with
      | .error (.scaleMismatch 0 2) => true
      | _ => false) = true := by
  native_decide

example : outcomes? minimum .minimum = some [
    (addr minimum.id 1, .accepted (stored 3 0)),
    (addr minimum.id 2, .accepted (stored 0 0)),
    (addr minimum.id 3, .accepted (stored (-2) 0)),
    (addr minimum.id 4, .accepted (stored 0 0)),
    (addr minimum.id 5, .inheritedPoison .malformed),
    (addr minimum.id 6, .inheritedPoison .declaredConstraint),
    (addr minimum.id 7, .accepted (stored 4 0))
  ] := by native_decide

example : outcomes? maximum .maximum = some [
    (addr maximum.id 1, .accepted (stored 525 2)),
    (addr maximum.id 2, .accepted (stored 525 2)),
    (addr maximum.id 3, .accepted (stored 0 0)),
    (addr maximum.id 4, .accepted (stored 0 0)),
    (addr maximum.id 5, .inheritedPoison .malformed),
    (addr maximum.id 6, .inheritedPoison .declaredConstraint),
    (addr maximum.id 7, .rejected (stored 12 0) .aboveMaximum)
  ] := by native_decide

example :
    (do
      let view ← result? [
        decimalCell maximum.id 1 "5.25" 525 2 (.parsed (.num (21 / 4))),
        decimalCell maximum.id 2 "1.00" 100 2 (.parsed (.num 1)),
        decimalCell maximum.id 5 "7.00" 700 2 (.parsed (.num 7))
      ]
      pure (view.withChanges.map (·.targetField), view.cleared,
        view.withErrors.map (·.targetField))) =
      some (
        [addr maximum.id 2, addr maximum.id 3, addr maximum.id 4],
        [addr maximum.id 5],
        [addr maximum.id 7]) := by
  native_decide

end A12Kernel.Conformance.AddressedNumberExtremum
