import A12Kernel.Elaboration.AddressedNumberDivision

/-! # Same-scope repeatable direct-Number division locks -/

namespace A12Kernel.Conformance.AddressedNumberDivision

open A12Kernel

private def number (id : FieldId) (name : String) : FlatFieldDecl := {
  id
  groupPath := ["Probe", "Rows"]
  name
  policy := { kind := .number { scale := 2, signed := true } }
  repeatableScope := [10]
}

private def left := number 1 "A"
private def right : FlatFieldDecl := {
  number 2 "B" with
  numericTargetConstraints := { maximum := some 10 }
}
private def quotient : FlatFieldDecl := {
  number 3 "Quotient" with
  numericTargetConstraints := {
    minFractionalDigits := 2
    maximum := some 3
  }
}

private def model : FlatModel := {
  fields := [left, right, quotient]
  repeatableGroups := [{
    level := 10
    path := ["Probe", "Rows"]
    repeatability := some 8
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

private def input? (extra : List ClassifiedCellInput := []) :
    Option (CheckedDocument model) :=
  (checkDocument prepared "en_US" {
    instantiatedRows := (List.range 8).map fun i =>
      { group := 10, path := [i + 1] }
    cells := [
      cell left.id 1 "10" (.parsed (.num 10)),
      cell right.id 1 "4" (.parsed (.num 4)),
      cell right.id 2 "5" (.parsed (.num 5)),
      cell left.id 3 "5" (.parsed (.num 5)),
      cell left.id 5 "bad-left" (.rejected .malformed),
      cell right.id 5 "2" (.parsed (.num 2)),
      cell left.id 6 "4" (.parsed (.num 4)),
      cell right.id 6 "12" (.rejected .declaredConstraint),
      cell left.id 7 "10" (.parsed (.num 10)),
      cell right.id 7 "3" (.parsed (.num 3)),
      cell left.id 8 "10" (.parsed (.num 10)),
      cell right.id 8 "2" (.parsed (.num 2))
    ] ++ extra
  }).toOption

private def checked? (suppression : Bool) :
    Option (CheckedAddressedNumberDivision model) :=
  (checkAddressedNumberDivision model ["Probe", "Rows"] quotient.id
    (bare "A") (bare "B") suppression).toOption

private def addr (field : FieldId) (row : Nat) : CellAddr :=
  { field, path := [row] }

private def stored (unscaled : Int) (scale : Nat) : StoredNumber :=
  { unscaled, scale }

private def pointer (row : Nat) : MessagePointer :=
  MessagePointer.ofCellAddr (addr quotient.id row)

private def outcomes? : Option (List (CellAddr × NumericTargetOutcome)) := do
  let operation ← checked? true
  let input ← input?
  let outcomes ← (operation.execute input).toOption
  pure (outcomes.map fun entry => (entry.targetField, entry.outcome))

private def result? (extra : List ClassifiedCellInput) :
    Option (NumericComputationRunView
      (ComputationFormalMessage Unit) CellAddr) := do
  let operation ← checked? true
  let input ← input? extra
  (operation.executeResult input (fun _ => ()) []).toOption

example :
    (checked? true).isSome = true ∧
    (match checkAddressedNumberDivision model ["Probe", "Rows"] quotient.id
        (bare "A") (bare "B") false with
      | .error .scaleSuppressionRequired => true
      | _ => false) = true := by
  native_decide

example : outcomes? = some [
    (addr quotient.id 1, .accepted (stored 250 2)),
    (addr quotient.id 2, .accepted (stored 0 2)),
    (addr quotient.id 3, .invalidNoValue .calculationValue),
    (addr quotient.id 4, .invalidNoValue .calculationValue),
    (addr quotient.id 5, .inheritedPoison .malformed),
    (addr quotient.id 6, .inheritedPoison .declaredConstraint),
    (addr quotient.id 7,
      .rejected (stored 3333333333333333 15) .totalDigitsTooLong),
    (addr quotient.id 8, .rejected (stored 500 2) .aboveMaximum)
  ] := by native_decide

example :
    (do
      let view ← result? [
        decimalCell quotient.id 1 "2.50" 250 2 (.parsed (.num (5 / 2))),
        decimalCell quotient.id 2 "1.00" 100 2 (.parsed (.num 1)),
        decimalCell quotient.id 3 "2.00" 200 2 (.parsed (.num 2)),
        decimalCell quotient.id 5 "2.00" 200 2 (.parsed (.num 2))
      ]
      pure (view.withChanges.map (·.targetField), view.cleared,
        view.withErrors.map (·.targetField),
        view.formalErrorsInOperands.map (·.pointer))) =
      some (
        [addr quotient.id 2],
        [addr quotient.id 3, addr quotient.id 5],
        [addr quotient.id 7, addr quotient.id 8],
        [pointer 3, pointer 4]) := by
  native_decide

end A12Kernel.Conformance.AddressedNumberDivision
