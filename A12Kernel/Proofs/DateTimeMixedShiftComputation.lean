import A12Kernel.Elaboration.DateTimeMixedShiftComputation

/-! # Checked mixed DateTime shift computation laws -/

namespace A12Kernel

/-- A mixed value transports its exact final instant into target rendering. -/
theorem dateTimeDayThenSubdayShiftComputation_value
    (operation : CheckedDateTimeDayThenSubdayShiftComputation model)
    (input : CheckedDocument model)
    (localDateTime : LocalDateTime) (instant : Instant) (notGiven : Bool)
    (shift :
      operation.shift.evaluateThenSubday operation.nextUnit
          operation.nextAmount .computation input =
        .ok (.value localDateTime instant notGiven)) :
    operation.evaluateOutcome input =
      (operation.target.evaluate (.value instant)).mapError .target := by
  simp [CheckedDateTimeDayThenSubdayShiftComputation.evaluateOutcome,
    CheckedDateTimeDayThenSubdayShiftComputation.evaluateOperand, shift,
    ValueAsDateTimeResult.asTemporalComputationResult]

/-- A reached source or amount cause remains target poison. -/
theorem dateTimeDayThenSubdayShiftComputation_unavailable
    (operation : CheckedDateTimeDayThenSubdayShiftComputation model)
    (input : CheckedDocument model) (cause : FormalCause)
    (shift :
      operation.shift.evaluateThenSubday operation.nextUnit
          operation.nextAmount .computation input =
        .ok (.unavailable cause)) :
    operation.evaluateOutcome input = .ok (.poison cause) := by
  unfold CheckedDateTimeDayThenSubdayShiftComputation.evaluateOutcome
  simp only [
    CheckedDateTimeDayThenSubdayShiftComputation.evaluateOperand, shift,
    ValueAsDateTimeResult.asTemporalComputationResult]
  change
    Except.mapError DateTimeMixedShiftComputationFault.target
      (.ok (.poison cause) :
        Except DateTimeTargetEvaluationFault DateTimeTargetOutcome) =
      .ok (.poison cause)
  rfl

/-- Calendar mutation and target rendering select one model-zone profile. -/
theorem dateTimeDayThenSubdayShiftComputation_profiles_eq
    (operation : CheckedDateTimeDayThenSubdayShiftComputation model) :
    operation.shift.profile = operation.target.profile := by
  have selected :
      some operation.shift.profile = some operation.target.profile :=
    operation.shift.profileMatches.symm.trans
      operation.target.profileMatches
  exact Option.some.inj selected

end A12Kernel
