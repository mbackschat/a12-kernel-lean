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

end A12Kernel
