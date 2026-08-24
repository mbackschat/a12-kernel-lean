import A12Kernel.Elaboration.DateFromDateTime

/-! # Checked `DateFromDateTime` computation laws -/

namespace A12Kernel

/-- Source extraction and target rendering use the same model-zone profile. -/
theorem dateFromDateTimeComputation_profiles_eq
    (operation : CheckedDateFromDateTimeComputation model) :
    operation.source.profile = operation.target.profile := by
  have selected :
      some operation.source.profile = some operation.target.profile := by
    simpa [CheckedTemporalTargetPolicy.timeZoneId] using
      operation.source.profileOwned.symm.trans operation.target.profileMatches
  exact Option.some.inj selected

/-- A computation-phase empty source remains clean no-value through target execution. -/
theorem dateFromDateTimeComputation_empty
    (operation : CheckedDateFromDateTimeComputation model)
    (input : CheckedDocument model)
    (read : input.read {
      field := operation.source.source.id, path := [] } = .ok cell)
    (empty : observeCell .computation cell = .empty) :
    operation.evaluateOutcome input = .ok .noValue := by
  have operandRead : operation.evaluateOperand input = .ok .noValue := by
    simp [CheckedDateFromDateTimeComputation.evaluateOperand, read, empty] <;> rfl
  unfold CheckedDateFromDateTimeComputation.evaluateOutcome
  rw [operandRead]
  rfl

/-- A reached formal source failure preserves its exact cause and never becomes a target error. -/
theorem dateFromDateTimeComputation_poison
    (operation : CheckedDateFromDateTimeComputation model)
    (input : CheckedDocument model)
    (read : input.read {
      field := operation.source.source.id, path := [] } = .ok cell)
    (poison : observeCell .computation cell = .poison cause) :
    operation.evaluateOutcome input = .ok (.poison cause) := by
  have operandRead :
      operation.evaluateOperand input = .ok (.poison cause) := by
    simp [CheckedDateFromDateTimeComputation.evaluateOperand, read, poison] <;> rfl
  unfold CheckedDateFromDateTimeComputation.evaluateOutcome
  rw [operandRead]
  rfl

/-- A present DateTime transports the extractor's own Date midnight into the declaration-owned target. -/
theorem dateFromDateTimeComputation_value
    (operation : CheckedDateFromDateTimeComputation model)
    (input : CheckedDocument model)
    (value : TemporalValue) (date : DateValue)
    (read : input.read {
      field := operation.source.source.id, path := [] } = .ok cell)
    (observed :
      observeCell .computation cell = .value (.temporal value))
    (extracted : operation.source.extract? value = some date) :
    operation.evaluateOutcome input =
      (operation.target.evaluate (.value date.instant)).mapError .target := by
  have operandRead :
      operation.evaluateOperand input = .ok (.value date.instant) := by
    simp [CheckedDateFromDateTimeComputation.evaluateOperand,
      read, observed, extracted] <;> rfl
  unfold CheckedDateFromDateTimeComputation.evaluateOutcome
  rw [operandRead]

end A12Kernel
