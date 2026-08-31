import A12Kernel.Elaboration.StringNumberComputationRunView

/-! # Family-preserving String and Number result locks -/

namespace A12Kernel.Conformance.StringNumberComputationRunView

open A12Kernel

private def storedString (text : String) (nonempty : text ≠ "") :
    StoredString :=
  { text, nonempty }

private def storedNumber (amount : Int) : StoredNumber :=
  { unscaled := amount, scale := 0 }

private def emptyStringView : StringComputationRunView Unit Nat :=
  StringComputationRunView.fromSourcedOutcomes [] []

private def emptyNumberView :
    NumericComputationRunView (ComputationFormalMessage Unit) Nat :=
  NumericComputationRunView.fromPartitionedSourceOutcomes [] []

private def cleanActionView : StringNumberComputationRunView Unit Unit Nat := {
  string := StringComputationRunView.fromSourcedOutcomes [] [{
    targetField := 1
    outcome := .accepted (storedString "NEW" (by decide))
    source := .absent
  }, {
    targetField := 2
    outcome := .noValue
    source := .presentValue (storedString "OLD" (by decide))
  }]
  number := NumericComputationRunView.fromPartitionedSourceOutcomes [] [{
    targetField := 3
    outcome := .accepted (storedNumber 7)
    source := .absent
  }, {
    targetField := 4
    outcome := .noValue
    source := .presentValue (.decimal (storedNumber 8))
  }]
}

private def stringComputedErrorView :
    StringNumberComputationRunView Unit Unit Nat := {
  string := StringComputationRunView.fromSourcedOutcomes [] [{
    targetField := 1
    outcome := .errored (storedString "LONG" (by decide)) .tooLong
    source := .absent
  }]
  number := emptyNumberView
}

private def stringResidualView :
    StringNumberComputationRunView Unit Unit Nat := {
  string := StringComputationRunView.fromSourcedOutcomes [()] []
  number := emptyNumberView
}

private def numberComputedErrorView :
    StringNumberComputationRunView Unit Unit Nat := {
  string := emptyStringView
  number := NumericComputationRunView.fromPartitionedSourceOutcomes [] [{
    targetField := 2
    outcome := .rejected (storedNumber 9) .aboveMaximum
    source := .absent
  }]
}

private def numberMessage : ComputationFormalMessage Unit := {
  pointer := { field := 2, coordinates := [] }
  errorCode := berechnungsWertFehler
  messageType := .value
  payload := ()
}

private def numberResidualView :
    StringNumberComputationRunView Unit Unit Nat := {
  string := emptyStringView
  number := NumericComputationRunView.fromPartitionedSourceOutcomes
    [numberMessage] []
}

/- Successful changes and clears in both families leave the combined status clean. -/
example : cleanActionView.noErrorOccurred = true := by
  native_decide

/- Either String error channel makes the combined status false while Number stays clean. -/
example :
    stringComputedErrorView.noErrorOccurred = false ∧
      stringResidualView.noErrorOccurred = false := by
  native_decide

/- The two Number error channels symmetrically make the combined status false. -/
example :
    numberComputedErrorView.noErrorOccurred = false ∧
      numberResidualView.noErrorOccurred = false := by
  native_decide

end A12Kernel.Conformance.StringNumberComputationRunView
