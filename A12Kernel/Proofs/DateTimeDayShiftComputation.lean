import A12Kernel.Elaboration.DateTimeDayShiftComputation

/-! # Checked DateTime day-shift computation laws -/

namespace A12Kernel

/-- A value-producing shift transports its exact instant into declaration-owned target
    rendering; its carried wall label and omission provenance cannot replace it. -/
theorem dateTimeDayShiftComputation_value
    (operation : CheckedDateTimeDayShiftComputation model)
    (input : CheckedDocument model)
    (localDateTime : LocalDateTime) (instant : Instant)
    (notGiven : Bool)
    (shift :
      operation.shift.evaluate .computation input =
        .ok (.value localDateTime instant notGiven)) :
    operation.evaluateOutcome input =
      (operation.target.evaluate (.value instant)).mapError .target := by
  simp [CheckedDateTimeDayShiftComputation.evaluateOutcome,
    CheckedDateTimeDayShiftComputation.evaluateOperand, shift,
    ValueAsDateTimeResult.asTemporalComputationResult]

/-- A reached formal source or amount cause remains target poison and does not become a
    target-local error. -/
theorem dateTimeDayShiftComputation_unavailable
    (operation : CheckedDateTimeDayShiftComputation model)
    (input : CheckedDocument model) (cause : FormalCause)
    (shift :
      operation.shift.evaluate .computation input =
        .ok (.unavailable cause)) :
    operation.evaluateOutcome input = .ok (.poison cause) := by
  unfold CheckedDateTimeDayShiftComputation.evaluateOutcome
  simp only [CheckedDateTimeDayShiftComputation.evaluateOperand, shift,
    ValueAsDateTimeResult.asTemporalComputationResult]
  change
    Except.mapError DateTimeDayShiftComputationFault.target
      (.ok (.poison cause) :
        Except DateTimeTargetEvaluationFault DateTimeTargetOutcome) =
      .ok (.poison cause)
  rfl

/-- Source mutation and target rendering select the same concrete model-zone profile. -/
theorem dateTimeDayShiftComputation_profiles_eq
    (operation : CheckedDateTimeDayShiftComputation model) :
    operation.shift.profile = operation.target.profile := by
  have selected :
      some operation.shift.profile = some operation.target.profile :=
    operation.shift.profileMatches.symm.trans
      operation.target.profileMatches
  exact Option.some.inj selected

/-- A dynamic value-producing shift transports the exact instant selected from this
    call's world into declaration-owned target rendering. -/
theorem nowDateTimeDayShiftComputation_value
    (operation : CheckedNowDateTimeDayShiftComputation model)
    (world : World) (input : CheckedDocument model)
    (localDateTime : LocalDateTime) (instant : Instant)
    (notGiven : Bool)
    (shift :
      operation.shift.evaluate .computation world input =
        .ok (.value localDateTime instant notGiven)) :
    operation.evaluateOutcome world input =
      (operation.target.evaluate (.value instant)).mapError .target := by
  simp [CheckedNowDateTimeDayShiftComputation.evaluateOutcome,
    CheckedNowDateTimeDayShiftComputation.evaluateOperand, shift,
    ValueAsDateTimeResult.asTemporalComputationResult]

/-- A reached formal dynamic amount cause remains target poison. -/
theorem nowDateTimeDayShiftComputation_unavailable
    (operation : CheckedNowDateTimeDayShiftComputation model)
    (world : World) (input : CheckedDocument model) (cause : FormalCause)
    (shift :
      operation.shift.evaluate .computation world input =
        .ok (.unavailable cause)) :
    operation.evaluateOutcome world input = .ok (.poison cause) := by
  unfold CheckedNowDateTimeDayShiftComputation.evaluateOutcome
  simp only [CheckedNowDateTimeDayShiftComputation.evaluateOperand, shift,
    ValueAsDateTimeResult.asTemporalComputationResult]
  change
    Except.mapError DateTimeDayShiftComputationFault.target
      (.ok (.poison cause) :
        Except DateTimeTargetEvaluationFault DateTimeTargetOutcome) =
      .ok (.poison cause)
  rfl

/-- Dynamic source mutation and target rendering select the same model-zone profile. -/
theorem nowDateTimeDayShiftComputation_profiles_eq
    (operation : CheckedNowDateTimeDayShiftComputation model) :
    operation.shift.profile = operation.target.profile := by
  have selected :
      some operation.shift.profile = some operation.target.profile :=
    operation.shift.profileMatches.symm.trans
      operation.target.profileMatches
  exact Option.some.inj selected

/-- A value-producing field-backed two-day continuation transports its exact instant
    into declaration-owned target rendering. -/
theorem dateTimeTwoDayShiftComputation_value
    (operation : CheckedDateTimeTwoDayShiftComputation model)
    (input : CheckedDocument model)
    (localDateTime : LocalDateTime) (instant : Instant)
    (notGiven : Bool)
    (shift :
      operation.shift.evaluateThen operation.nextAmount
          .computation input =
        .ok (.value localDateTime instant notGiven)) :
    operation.evaluateOutcome input =
      (operation.target.evaluate (.value instant)).mapError .target := by
  simp [CheckedDateTimeTwoDayShiftComputation.evaluateOutcome,
    CheckedDateTimeTwoDayShiftComputation.evaluateOperand, shift,
    ValueAsDateTimeResult.asTemporalComputationResult]

/-- A reached formal cause from the source or either day amount remains target poison. -/
theorem dateTimeTwoDayShiftComputation_unavailable
    (operation : CheckedDateTimeTwoDayShiftComputation model)
    (input : CheckedDocument model) (cause : FormalCause)
    (shift :
      operation.shift.evaluateThen operation.nextAmount
          .computation input =
        .ok (.unavailable cause)) :
    operation.evaluateOutcome input = .ok (.poison cause) := by
  unfold CheckedDateTimeTwoDayShiftComputation.evaluateOutcome
  simp only [CheckedDateTimeTwoDayShiftComputation.evaluateOperand, shift,
    ValueAsDateTimeResult.asTemporalComputationResult]
  change
    Except.mapError DateTimeDayShiftComputationFault.target
      (.ok (.poison cause) :
        Except DateTimeTargetEvaluationFault DateTimeTargetOutcome) =
      .ok (.poison cause)
  rfl

/-- Field-backed two-day mutation and target rendering select one model-zone profile. -/
theorem dateTimeTwoDayShiftComputation_profiles_eq
    (operation : CheckedDateTimeTwoDayShiftComputation model) :
    operation.shift.profile = operation.target.profile := by
  have selected :
      some operation.shift.profile = some operation.target.profile :=
    operation.shift.profileMatches.symm.trans
      operation.target.profileMatches
  exact Option.some.inj selected

/-- A value-producing dynamic two-day continuation transports its exact instant into
    declaration-owned target rendering. -/
theorem nowDateTimeTwoDayShiftComputation_value
    (operation : CheckedNowDateTimeTwoDayShiftComputation model)
    (world : World) (input : CheckedDocument model)
    (localDateTime : LocalDateTime) (instant : Instant)
    (notGiven : Bool)
    (shift :
      operation.shift.evaluateThen operation.nextAmount
          .computation world input =
        .ok (.value localDateTime instant notGiven)) :
    operation.evaluateOutcome world input =
      (operation.target.evaluate (.value instant)).mapError .target := by
  simp [CheckedNowDateTimeTwoDayShiftComputation.evaluateOutcome,
    CheckedNowDateTimeTwoDayShiftComputation.evaluateOperand, shift,
    ValueAsDateTimeResult.asTemporalComputationResult]

/-- A reached formal cause from either day amount remains target poison. -/
theorem nowDateTimeTwoDayShiftComputation_unavailable
    (operation : CheckedNowDateTimeTwoDayShiftComputation model)
    (world : World) (input : CheckedDocument model) (cause : FormalCause)
    (shift :
      operation.shift.evaluateThen operation.nextAmount
          .computation world input =
        .ok (.unavailable cause)) :
    operation.evaluateOutcome world input = .ok (.poison cause) := by
  unfold CheckedNowDateTimeTwoDayShiftComputation.evaluateOutcome
  simp only [CheckedNowDateTimeTwoDayShiftComputation.evaluateOperand, shift,
    ValueAsDateTimeResult.asTemporalComputationResult]
  change
    Except.mapError DateTimeDayShiftComputationFault.target
      (.ok (.poison cause) :
        Except DateTimeTargetEvaluationFault DateTimeTargetOutcome) =
      .ok (.poison cause)
  rfl

/-- Dynamic two-day mutation and target rendering select the same model-zone profile. -/
theorem nowDateTimeTwoDayShiftComputation_profiles_eq
    (operation : CheckedNowDateTimeTwoDayShiftComputation model) :
    operation.shift.profile = operation.target.profile := by
  have selected :
      some operation.shift.profile = some operation.target.profile :=
    operation.shift.profileMatches.symm.trans
      operation.target.profileMatches
  exact Option.some.inj selected

end A12Kernel
