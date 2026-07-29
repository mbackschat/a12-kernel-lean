import A12Kernel.Elaboration.TimeComputation

/-! # Checked Time target laws -/

namespace A12Kernel

@[simp] theorem timeConstructionResult_value
    (time : TimeOfDay) :
    (TimeConstructionResult.value time).asTimeComputationResult =
      .value time := rfl

@[simp] theorem timeConstructionResult_unavailable
    (cause : FormalCause) :
    (TimeConstructionResult.unavailable cause).asTimeComputationResult =
      .poison cause := rfl

/-- Every selected clock is retained exactly through target rendering. -/
theorem timeTarget_evaluate_value
    (target : CheckedTimeTarget model) (time : TimeOfDay) :
    target.evaluate (.value time) =
      .accepted (target.format.render time) := rfl

/-- Time has no target-local error branch, so only residual messages affect the public error predicate. -/
theorem timeComputationRun_noErrorOccurred_iff
    (view : TimeComputationRunView ResidualMessage) :
    view.noErrorOccurred = true ↔
      view.formalErrorsInOperands = [] := by
  have noComputedErrors : view.withErrors = [] := by
    cases errorList : view.withErrors with
    | nil => rfl
    | cons error _ => exact nomatch error
  simp [TimeComputationRunView.noErrorOccurred,
    TemporalComputationRunView.noErrorOccurred, noComputedErrors]

/-- Residual messages never change already-classified Time application actions. -/
theorem timeComputationRun_residualMessages_doNotAffectApplication
    (input : CheckedDocument model)
    (firstMessages secondMessages : List ResidualMessage)
    (outcomes : List (FieldId × TimeTargetOutcome))
    (destination : TimeComputationDestination) :
    (TimeComputationRunView.fromOutcomes input firstMessages outcomes).applyTo
        destination =
      (TimeComputationRunView.fromOutcomes input secondMessages outcomes).applyTo
        destination := by
  rfl

end A12Kernel
