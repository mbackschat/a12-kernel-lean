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

private def numberMessageAt (field payload : Nat) :
    ComputationFormalMessage Nat := {
  pointer := { field, coordinates := [] }
  errorCode := berechnungsWertFehler
  messageType := .value
  payload
}

private def stringEntries (second : StoredString) :
    List (SourcedStringTargetOutcome Nat) := [{
    targetField := 1
    outcome := .accepted (storedString "ONE" (by decide))
    source := .absent
  }, {
    targetField := 2
    outcome := .accepted second
    source := .absent
  }, {
    targetField := 5
    outcome := .errored (storedString "FIVE" (by decide)) .tooLong
    source := .absent
  }, {
    targetField := 6
    outcome := .errored (storedString "SIX" (by decide)) .tooLong
    source := .absent
  }, {
    targetField := 7
    outcome := .noValue
    source := .presentValue (storedString "OLD7" (by decide))
  }, {
    targetField := 8
    outcome := .noValue
    source := .presentValue (storedString "OLD8" (by decide))
  }]

private def numberEntries (second : StoredNumber) :
    List (SourcedNumericTargetOutcome Nat) := [{
    targetField := 3
    outcome := .accepted (storedNumber 3)
    source := .absent
  }, {
    targetField := 4
    outcome := .accepted second
    source := .absent
  }, {
    targetField := 9
    outcome := .rejected (storedNumber 9) .aboveMaximum
    source := .absent
  }, {
    targetField := 10
    outcome := .rejected (storedNumber 10) .aboveMaximum
    source := .absent
  }, {
    targetField := 11
    outcome := .noValue
    source := .presentValue (.decimal (storedNumber 11))
  }, {
    targetField := 12
    outcome := .noValue
    source := .presentValue (.decimal (storedNumber 12))
  }]

private def orderedView :
    StringNumberComputationRunView Nat Nat Nat := {
  string := StringComputationRunView.fromSourcedOutcomes [10, 20]
    (stringEntries (storedString "TWO" (by decide)))
  number := NumericComputationRunView.fromPartitionedSourceOutcomes
    [numberMessageAt 3 30, numberMessageAt 4 40]
    (numberEntries (storedNumber 4))
}

private def reorderedView :
    StringNumberComputationRunView Nat Nat Nat := {
  string := StringComputationRunView.fromSourcedOutcomes [20, 10]
    (stringEntries (storedString "TWO" (by decide))).reverse
  number := NumericComputationRunView.fromPartitionedSourceOutcomes
    [numberMessageAt 4 40, numberMessageAt 3 30]
    (numberEntries (storedNumber 4)).reverse
}

private def differentStringView :
    StringNumberComputationRunView Nat Nat Nat := {
  orderedView with
  string := StringComputationRunView.fromSourcedOutcomes [10, 20]
    (stringEntries (storedString "OTHER" (by decide)))
}

private def differentNumberView :
    StringNumberComputationRunView Nat Nat Nat := {
  orderedView with
  number := NumericComputationRunView.fromPartitionedSourceOutcomes
    [numberMessageAt 3 30, numberMessageAt 4 40]
    (numberEntries (storedNumber 5))
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

/- Reordering every public collection in both families changes structural list equality but not the mixed extensional result. -/
example :
    orderedView ≠ reorderedView ∧
      StringNumberComputationRunView.ExtensionalEq
        orderedView reorderedView := by
  constructor
  · native_decide
  · simp [StringNumberComputationRunView.ExtensionalEq,
      orderedView, reorderedView,
      stringEntries, numberEntries,
      StringComputationRunView.ExtensionalEq,
      StringComputationRunView.fromSourcedOutcomes,
      StringComputationRunView.successfulInstance?,
      StringComputationRunView.changedInstance?,
      StringComputationRunView.computedError?,
      StringComputationRunView.shouldClear,
      StringTargetOutcome.hasComputedInstance,
      StringTargetState.storedValue,
      NumericComputationRunView.ExtensionalEq,
      NumericComputationRunView.fromPartitionedSourceOutcomes,
      NumericComputationRunView.successfulInstance?,
      NumericComputationRunView.changedInstance?,
      NumericComputationRunView.computedError?,
      NumericComputationRunView.shouldClear,
      NumericTargetOutcome.hasComputedInstance,
      NumericTargetState.sourceIdentity]
    exact ⟨
      ⟨List.Perm.swap _ _ [], List.Perm.swap _ _ [],
        List.Perm.swap _ _ [], List.Perm.swap _ _ []⟩,
      ⟨List.Perm.swap _ _ [], List.Perm.swap _ _ [],
        List.Perm.swap _ _ [], List.Perm.swap _ _ []⟩
    ⟩

/- A payload change in either retained family prevents mixed extensional equality. -/
example :
    ¬StringNumberComputationRunView.ExtensionalEq
        orderedView differentStringView ∧
      ¬StringNumberComputationRunView.ExtensionalEq
        orderedView differentNumberView := by
  constructor
  · intro equal
    let expected : StringComputedInstance Nat := {
      targetField := 2
      value := storedString "TWO" (by decide)
    }
    have leftMember : expected ∈ orderedView.string.withoutErrors := by
      native_decide
    have rightMember := equal.1.1.mem_iff.mp leftMember
    have absent :
        expected ∉ differentStringView.string.withoutErrors := by
      native_decide
    exact absent rightMember
  · intro equal
    let expected : NumericComputedInstance Nat := {
      targetField := 4
      value := storedNumber 4
    }
    have leftMember : expected ∈ orderedView.number.withoutErrors := by
      native_decide
    have rightMember := equal.2.1.mem_iff.mp leftMember
    have absent :
        expected ∉ differentNumberView.number.withoutErrors := by
      native_decide
    exact absent rightMember

end A12Kernel.Conformance.StringNumberComputationRunView
