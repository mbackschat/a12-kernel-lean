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

/-- A dynamic mixed value transports this call's exact final instant to the target. -/
theorem nowDateTimeDayThenSubdayShiftComputation_value
    (operation : CheckedNowDateTimeDayThenSubdayShiftComputation model)
    (world : World) (input : CheckedDocument model)
    (localDateTime : LocalDateTime) (instant : Instant) (notGiven : Bool)
    (shift :
      operation.shift.evaluateThenSubday operation.nextUnit
          operation.nextAmount .computation world input =
        .ok (.value localDateTime instant notGiven)) :
    operation.evaluateOutcome world input =
      (operation.target.evaluate (.value instant)).mapError .target := by
  simp [CheckedNowDateTimeDayThenSubdayShiftComputation.evaluateOutcome,
    CheckedNowDateTimeDayThenSubdayShiftComputation.evaluateOperand, shift,
    ValueAsDateTimeResult.asTemporalComputationResult]

/-- A reached dynamic amount cause remains target poison. -/
theorem nowDateTimeDayThenSubdayShiftComputation_unavailable
    (operation : CheckedNowDateTimeDayThenSubdayShiftComputation model)
    (world : World) (input : CheckedDocument model) (cause : FormalCause)
    (shift :
      operation.shift.evaluateThenSubday operation.nextUnit
          operation.nextAmount .computation world input =
        .ok (.unavailable cause)) :
    operation.evaluateOutcome world input = .ok (.poison cause) := by
  unfold CheckedNowDateTimeDayThenSubdayShiftComputation.evaluateOutcome
  simp only [
    CheckedNowDateTimeDayThenSubdayShiftComputation.evaluateOperand, shift,
    ValueAsDateTimeResult.asTemporalComputationResult]
  change
    Except.mapError DateTimeMixedShiftComputationFault.target
      (.ok (.poison cause) :
        Except DateTimeTargetEvaluationFault DateTimeTargetOutcome) =
      .ok (.poison cause)
  rfl

/-- Dynamic day mutation and target rendering select one model-zone profile. -/
theorem nowDateTimeDayThenSubdayShiftComputation_profiles_eq
    (operation : CheckedNowDateTimeDayThenSubdayShiftComputation model) :
    operation.shift.profile = operation.target.profile := by
  have selected :
      some operation.shift.profile = some operation.target.profile :=
    operation.shift.profileMatches.symm.trans
      operation.target.profileMatches
  exact Option.some.inj selected

/-- A reverse-order mixed value transports its exact final instant to the target. -/
theorem dateTimeSubdayThenDayShiftComputation_value
    (operation : CheckedDateTimeSubdayThenDayShiftComputation model)
    (input : CheckedDocument model)
    (localDateTime : LocalDateTime) (instant : Instant) (notGiven : Bool)
    (shift :
      operation.shift.evaluateThenDays operation.nextAmount
          .computation input =
        .ok (.value localDateTime instant notGiven)) :
    operation.evaluateOutcome input =
      (operation.target.evaluate (.value instant)).mapError .target := by
  simp [CheckedDateTimeSubdayThenDayShiftComputation.evaluateOutcome,
    CheckedDateTimeSubdayThenDayShiftComputation.evaluateOperand, shift,
    ValueAsDateTimeResult.asTemporalComputationResult]

/-- A reached source or amount cause remains target poison. -/
theorem dateTimeSubdayThenDayShiftComputation_unavailable
    (operation : CheckedDateTimeSubdayThenDayShiftComputation model)
    (input : CheckedDocument model) (cause : FormalCause)
    (shift :
      operation.shift.evaluateThenDays operation.nextAmount
          .computation input =
        .ok (.unavailable cause)) :
    operation.evaluateOutcome input = .ok (.poison cause) := by
  unfold CheckedDateTimeSubdayThenDayShiftComputation.evaluateOutcome
  simp only [
    CheckedDateTimeSubdayThenDayShiftComputation.evaluateOperand, shift,
    ValueAsDateTimeResult.asTemporalComputationResult]
  change
    Except.mapError DateTimeReverseMixedShiftComputationFault.target
      (.ok (.poison cause) :
        Except DateTimeTargetEvaluationFault DateTimeTargetOutcome) =
      .ok (.poison cause)
  rfl

/-- Reverse-order mutation and target rendering select one model-zone profile. -/
theorem dateTimeSubdayThenDayShiftComputation_profiles_eq
    (operation : CheckedDateTimeSubdayThenDayShiftComputation model) :
    operation.shift.profile = operation.target.profile := by
  have selected :
      some operation.shift.profile = some operation.target.profile :=
    operation.shift.profileMatches.symm.trans
      operation.target.profileMatches
  exact Option.some.inj selected

end A12Kernel
