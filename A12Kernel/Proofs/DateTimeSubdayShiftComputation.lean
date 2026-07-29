import A12Kernel.Elaboration.DateTimeSubdayShiftComputation

/-! # Checked DateTime sub-day computation laws -/

namespace A12Kernel

/-- A value-producing sub-day shift transports its exact instant into target rendering. -/
theorem dateTimeSubdayShiftComputation_value
    (operation : CheckedDateTimeSubdayShiftComputation model)
    (input : CheckedDocument model) (localDateTime : LocalDateTime)
    (instant : Instant) (notGiven : Bool)
    (shift : operation.shift.evaluate .computation input =
      .ok (.value localDateTime instant notGiven)) :
    operation.evaluateOutcome input =
      (operation.target.evaluate (.value instant)).mapError .target := by
  unfold CheckedDateTimeSubdayShiftComputation.evaluateOutcome
  unfold CheckedDateTimeSubdayShiftComputation.evaluateOperand
  rw [shift]
  simp [ValueAsDateTimeResult.asTemporalComputationResult]

/-- Shift and target certificates select the same model-zone profile. -/
theorem dateTimeSubdayShiftComputation_profiles_eq
    (operation : CheckedDateTimeSubdayShiftComputation model) :
    operation.shift.profile = operation.target.profile := by
  have selected :
      some operation.shift.profile = some operation.target.profile :=
    operation.shift.profileMatches.symm.trans operation.target.profileMatches
  exact Option.some.inj selected

end A12Kernel
