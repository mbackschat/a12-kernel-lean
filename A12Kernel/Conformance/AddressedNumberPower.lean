import A12Kernel.Elaboration.AddressedNumberPower

/-! # Same-scope repeatable direct-Number power locks -/

namespace A12Kernel.Conformance.AddressedNumberPower

open A12Kernel

private def number (id : FieldId) (name : String) (scale : Nat) : FlatFieldDecl := {
  id
  groupPath := ["Probe", "Rows"]
  name
  policy := { kind := .number { scale, signed := true } }
  repeatableScope := [10]
}

private def base := number 1 "Base" 2
private def exponent : FlatFieldDecl := {
  number 2 "Exponent" 0 with
  numericTargetConstraints := { minimum := some (-1001), maximum := some 1001 }
}
private def fractionalExponent := number 3 "FractionalExponent" 1
private def result : FlatFieldDecl := {
  number 4 "Result" 2 with
  numericTargetConstraints := {
    minFractionalDigits := 2
    maximum := some 3
  }
}

private def model : FlatModel := {
  fields := [base, exponent, fractionalExponent, result]
  repeatableGroups := [{
    level := 10
    path := ["Probe", "Rows"]
    repeatability := some 14
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
    instantiatedRows := (List.range 14).map fun i =>
      { group := 10, path := [i + 1] }
    cells := [
      decimalCell base.id 1 "1.50" 150 2 (.parsed (.num (3 / 2))),
      cell exponent.id 1 "2" (.parsed (.num 2)),
      cell exponent.id 2 "2" (.parsed (.num 2)),
      decimalCell base.id 3 "2.00" 200 2 (.parsed (.num 2)),
      decimalCell base.id 5 "0.00" 0 2 (.parsed (.num 0)),
      cell exponent.id 5 "-1" (.parsed (.num (-1))),
      decimalCell base.id 6 "2.00" 200 2 (.parsed (.num 2)),
      cell exponent.id 6 "1001" (.parsed (.num 1001)),
      decimalCell base.id 7 "1.00" 100 2 (.parsed (.num 1)),
      cell exponent.id 7 "1000" (.parsed (.num 1000)),
      decimalCell base.id 8 "1.00" 100 2 (.parsed (.num 1)),
      cell exponent.id 8 "-1000" (.parsed (.num (-1000))),
      decimalCell base.id 9 "1.23" 123 2 (.parsed (.num (123 / 100))),
      cell exponent.id 9 "2" (.parsed (.num 2)),
      decimalCell base.id 10 "2.00" 200 2 (.parsed (.num 2)),
      cell exponent.id 10 "2" (.parsed (.num 2)),
      cell base.id 11 "bad-base" (.rejected .malformed),
      cell exponent.id 11 "2" (.parsed (.num 2)),
      decimalCell base.id 12 "2.00" 200 2 (.parsed (.num 2)),
      cell exponent.id 12 "1002" (.rejected .declaredConstraint),
      decimalCell base.id 13 "2.00" 200 2 (.parsed (.num 2)),
      cell exponent.id 13 "-1" (.parsed (.num (-1))),
      decimalCell base.id 14 "0.00" 0 2 (.parsed (.num 0)),
      cell exponent.id 14 "0" (.parsed (.num 0))
    ] ++ extra
  }).toOption

private def checked? (exponentName : String := "Exponent")
    (suppression : Bool := true) :
    Option (CheckedAddressedNumberPower model) :=
  (checkAddressedNumberPower model ["Probe", "Rows"] result.id
    (bare "Base") (bare exponentName) suppression).toOption

private def addr (field : FieldId) (row : Nat) : CellAddr :=
  { field, path := [row] }

private def stored (unscaled : Int) (scale : Nat) : StoredNumber :=
  { unscaled, scale }

private def pointer (row : Nat) : MessagePointer :=
  MessagePointer.ofCellAddr (addr result.id row)

private def outcomes? : Option (List (CellAddr × NumericTargetOutcome)) := do
  let operation ← checked?
  let input ← input?
  let outcomes ← (operation.execute input).toOption
  pure (outcomes.map fun entry => (entry.targetField, entry.outcome))

private def result? (extra : List ClassifiedCellInput) :
    Option (NumericComputationRunView
      (ComputationFormalMessage Unit) CellAddr) := do
  let operation ← checked?
  let input ← input? extra
  (operation.executeResult input (fun _ => ()) []).toOption

example :
    (checked?).isSome = true ∧
    (match checkAddressedNumberPower model ["Probe", "Rows"] result.id
        (bare "Base") (bare "Exponent") false with
      | .error .scaleSuppressionRequired => true
      | _ => false) = true ∧
    (match checkAddressedNumberPower model ["Probe", "Rows"] result.id
        (bare "Base") (bare "FractionalExponent") true with
      | .error (.invalidExponentScale 1) => true
      | _ => false) = true := by
  native_decide

example : outcomes? = some [
    (addr result.id 1, .accepted (stored 225 2)),
    (addr result.id 2, .accepted (stored 0 2)),
    (addr result.id 3, .accepted (stored 100 2)),
    (addr result.id 4, .accepted (stored 100 2)),
    (addr result.id 5, .invalidNoValue .calculationValue),
    (addr result.id 6, .invalidNoValue .calculationValue),
    (addr result.id 7, .accepted (stored 100 2)),
    (addr result.id 8, .accepted (stored 100 2)),
    (addr result.id 9, .rejected (stored 15129 4) .suppressedScaleMismatch),
    (addr result.id 10, .rejected (stored 400 2) .aboveMaximum),
    (addr result.id 11, .inheritedPoison .malformed),
    (addr result.id 12, .inheritedPoison .declaredConstraint),
    (addr result.id 13, .accepted (stored 50 2)),
    (addr result.id 14, .accepted (stored 100 2))
  ] := by native_decide

example :
    (do
      let view ← result? [
        decimalCell result.id 1 "2.25" 225 2 (.parsed (.num (9 / 4))),
        decimalCell result.id 2 "2.00" 200 2 (.parsed (.num 2)),
        decimalCell result.id 5 "2.00" 200 2 (.parsed (.num 2)),
        decimalCell result.id 11 "2.00" 200 2 (.parsed (.num 2))
      ]
      pure (view.withChanges.map (·.targetField), view.cleared,
        view.withErrors.map (·.targetField),
        view.formalErrorsInOperands.map (·.pointer))) =
      some (
        [addr result.id 2, addr result.id 3, addr result.id 4,
          addr result.id 7, addr result.id 8, addr result.id 13,
          addr result.id 14],
        [addr result.id 5, addr result.id 11],
        [addr result.id 9, addr result.id 10],
        [pointer 5, pointer 6]) := by
  native_decide

end A12Kernel.Conformance.AddressedNumberPower
