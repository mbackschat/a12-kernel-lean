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

/-- The checked computation certificate excludes its target from every supplied component dependency. -/
theorem checkedTimeConstructionComputation_excludes_target
    (operation : CheckedTimeConstructionComputation model) :
    operation.components.referencesField
      operation.target.checked.target.id = false :=
  operation.targetNotReferenced

/-- A real checked construction reaches exact target rendering without an intermediate instant. -/
theorem checkedTimeConstructionComputation_evaluate_value
    (operation : CheckedTimeConstructionComputation model)
    (input : CheckedDocument model) (time : TimeOfDay)
    (evaluated :
      operation.evaluateConstruction input = .ok (.value time)) :
    operation.evaluateOutcome input =
      .ok (.accepted (operation.target.format.render time)) := by
  simp [CheckedTimeConstructionComputation.evaluateOutcome, evaluated,
    TimeConstructionResult.asTimeComputationResult,
    CheckedTimeTarget.evaluate, Except.map]

/-- The checked world-aware computation certificate excludes its target from every static component and dynamic amount dependency. -/
theorem checkedWorldTimeConstructionComputation_excludes_target
    (operation : CheckedWorldTimeConstructionComputation model) :
    operation.components.referencesField
      operation.target.checked.target.id = false :=
  operation.targetNotReferenced

/-- A real world-aware construction reaches exact target rendering without retaining the transport date or instant. -/
theorem checkedWorldTimeConstructionComputation_evaluate_value
    (operation : CheckedWorldTimeConstructionComputation model)
    (world : World) (input : CheckedDocument model) (time : TimeOfDay)
    (evaluated :
      operation.evaluateConstruction world input = .ok (.value time)) :
    operation.evaluateOutcome world input =
      .ok (.accepted (operation.target.format.render time)) := by
  simp [CheckedWorldTimeConstructionComputation.evaluateOutcome, evaluated,
    TimeConstructionResult.asTimeComputationResult,
    CheckedTimeTarget.evaluate, Except.map]

/-- Time has no target-local error branch, so only residual messages affect the public error predicate. -/
theorem timeComputationRun_noErrorOccurred_iff
    (view : TimeComputationRunView ResidualMessage Target) :
    view.noErrorOccurred = true ↔
      view.formalErrorsInOperands = [] := by
  have noComputedErrors : view.withErrors = [] := by
    cases errorList : view.withErrors with
    | nil => rfl
    | cons error _ => exact nomatch error
  simp [TimeComputationRunView.noErrorOccurred,
    TemporalComputationRunView.noErrorOccurred, noComputedErrors]

/-- Every successful Time instance enters the kernel's source-relative changed subset, even when its stored clock text equals the source. -/
@[simp] theorem timeComputationRun_reportsChanged
    (computed : TimeComputedInstance Target) :
    TimeComputationRunView.reportsChanged computed = true := rfl

/-- A retained Time clear creates a present-empty destination target even when that target was absent. -/
theorem timeComputationDestination_applyRetainedClear_same
    {Target : Type} [DecidableEq Target]
    (destination : TimeComputationDestination Target)
    (target : Target) :
    destination.applyRetainedClear target target = .presentEmpty := by
  simp [TimeComputationDestination.applyRetainedClear,
    TemporalComputationDestination.applyRetainedClear,
    TemporalComputationDestination.update,
    TemporalTargetState.applyRetainedClear]
  cases destination target <;> rfl

/-- A checked Time application with admitted unique targets delegates exactly to the established value/clear fold over the checked document's source projection. -/
theorem timeComputationRun_applyToChecked_delegates
    (view : TimeComputationRunView ResidualMessage)
    (destination : CheckedDocument model)
    (unique : FieldId.firstDuplicate? view.actionTargets = none)
    (valid : TimeComputationRunView.validateActionTargets model
      view.actionTargets = .ok ()) :
    view.applyToChecked destination =
      (view.applyTo destination.sourceTimeTargetState).mapError
        (fun | .duplicateActionTarget duplicate => TimeComputationRunView.TimeComputationCheckedApplicationError.duplicateActionTarget duplicate) := by
  simp [TimeComputationRunView.applyToChecked, unique, valid]
  rfl

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
