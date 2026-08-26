import A12Kernel.Elaboration.EnumerationComputationResult

/-! # Ordinary Enumeration computation result and application laws -/

namespace A12Kernel

private theorem oneTargetStringResult_actionsOwned
    (target : FieldId) (outcome : StringTargetOutcome)
    (source : StringTargetState) (residualMessages : List ResidualMessage) :
    (StringComputationRunView.fromSourcedOutcomes residualMessages [{
      targetField := target
      outcome
      source
    }]).actionTargets.all (· == target) = true := by
  cases outcome with
  | accepted value =>
      cases source with
      | absent | presentEmpty =>
          simp [StringComputationRunView.actionTargets,
            StringComputationRunView.fromSourcedOutcomes,
            StringComputationRunView.changedInstance?,
            StringComputationRunView.successfulInstance?,
            StringComputationRunView.computedError?,
            StringComputationRunView.shouldClear,
            StringTargetState.storedValue]
      | presentValue prior =>
          by_cases same : prior = value <;>
            simp [StringComputationRunView.actionTargets,
              StringComputationRunView.fromSourcedOutcomes,
              StringComputationRunView.changedInstance?,
              StringComputationRunView.successfulInstance?,
              StringComputationRunView.computedError?,
              StringComputationRunView.shouldClear,
              StringTargetState.storedValue, same]
  | noValue | errored _ _ | poison _ =>
      cases source <;>
        simp [StringComputationRunView.actionTargets,
          StringComputationRunView.fromSourcedOutcomes,
          StringComputationRunView.changedInstance?,
          StringComputationRunView.successfulInstance?,
          StringComputationRunView.computedError?,
          StringComputationRunView.shouldClear,
          StringTargetOutcome.hasComputedInstance]

/-- Result construction retains the exact model-certified Enumeration target. -/
theorem checkedEnumerationComputation_executeResult_target
    (operation : CheckedEnumerationComputationOperation model)
    (input : CheckedDocument model) (residualMessages : List ResidualMessage) :
    (operation.executeResult input residualMessages).target = operation.target := by
  rfl

/-- Static Enumeration-domain compatibility makes a runtime target-rejection channel impossible; exact values, no-value, and source poison still use the other shared String-shaped channels. -/
theorem checkedEnumerationComputation_executeResult_hasNoTargetErrors
    (operation : CheckedEnumerationComputationOperation model)
    (input : CheckedDocument model) (residualMessages : List ResidualMessage) :
    (operation.executeResult input residualMessages).string.withErrors = [] := by
  cases evaluated : operation.source.evaluate input.flatContext with
  | value token =>
      by_cases empty : token = ""
      · simp [CheckedEnumerationComputationOperation.executeResult, evaluated,
          TokenComputationResult.asEnumerationTargetOutcome, empty,
          StringComputationRunView.fromSourcedOutcomes,
          StringComputationRunView.computedError?]
      · simp [CheckedEnumerationComputationOperation.executeResult, evaluated,
          TokenComputationResult.asEnumerationTargetOutcome, empty,
          StringComputationRunView.fromSourcedOutcomes,
          StringComputationRunView.computedError?]
  | noValue =>
      simp [CheckedEnumerationComputationOperation.executeResult, evaluated,
        TokenComputationResult.asEnumerationTargetOutcome,
        StringComputationRunView.fromSourcedOutcomes,
        StringComputationRunView.computedError?]
  | poison cause =>
      simp [CheckedEnumerationComputationOperation.executeResult, evaluated,
        TokenComputationResult.asEnumerationTargetOutcome,
        StringComputationRunView.fromSourcedOutcomes,
        StringComputationRunView.computedError?]

/-- Every retained action from ordinary Enumeration result construction names its exact certified target. -/
theorem checkedEnumerationComputation_executeResult_actionsOwned
    (operation : CheckedEnumerationComputationOperation model)
    (input : CheckedDocument model) (residualMessages : List ResidualMessage) :
    (operation.executeResult input residualMessages).string.actionTargets.all
      (· == operation.target.field) = true := by
  apply oneTargetStringResult_actionsOwned

/-- Model-indexed checked Enumeration application delegates exactly to the established source-classified String fold over the separately supplied destination. -/
theorem enumerationComputationRun_applyToChecked_delegates
    (view : EnumerationComputationRunView model ResidualMessage)
    (destination : CheckedDocument model) :
    view.applyToChecked destination =
      view.string.applyTo destination.sourceStringTargetState := by
  rfl

end A12Kernel
