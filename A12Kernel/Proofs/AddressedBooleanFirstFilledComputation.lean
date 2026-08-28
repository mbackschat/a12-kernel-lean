import A12Kernel.Elaboration.AddressedBooleanFirstFilledFormalInput

/-! # Exact-address repeatable Boolean `FirstFilledValue` laws -/

namespace A12Kernel

/-- The checked source has exactly one reopened star axis and a nonempty outer prefix supplied by the target scope. -/
theorem checkedAddressedBooleanFirstFilled_source_bounded
    (operation : CheckedAddressedBooleanFirstFilledComputation model) :
    operation.source.declaration.policy.kind = .boolean ∧
      operation.source.reopenedScope.length = 1 ∧
      operation.source.bindingScope ≠ [] ∧
      operation.source.bindingScope.all
        operation.target.repeatableScope.contains = true :=
  ⟨operation.sourceBoolean, operation.sourceSingleReopenedAxis,
    operation.sourceBindingNonempty, operation.sourceBindingBound⟩

/-- The immutable-document executor is definitionally the caller-read route specialized to the document's checked read. -/
theorem checkedAddressedBooleanFirstFilled_executeWithRead_base
    (operation : CheckedAddressedBooleanFirstFilledComputation model)
    (input : CheckedDocument model) :
    operation.executeWithRead input input.read = operation.execute input := by
  rfl

/-- Addressed result construction retains the checked operation and classifies every outcome against its exact immutable target state. -/
theorem checkedAddressedBooleanFirstFilled_executeResult_projects
    (operation : CheckedAddressedBooleanFirstFilledComputation model)
    (input : CheckedDocument model) (messages : List ResidualMessage)
    (outcomes : List AddressedBooleanFirstFilledComputationOutcome)
    (view : AddressedBooleanFirstFilledComputationRunView model ResidualMessage)
    (executed : operation.execute input = .ok outcomes)
    (produced : operation.executeResult input messages = .ok view) :
    view.operation = operation ∧
      view.boolean = BooleanComputationRunView.fromSourcedOutcomes messages
        (outcomes.map fun entry =>
          (entry.targetField, entry.result,
            input.sourceBooleanTargetStateAt entry.targetField)) := by
  rw [CheckedAddressedBooleanFirstFilledComputation.executeResult,
    CheckedAddressedBooleanFirstFilledComputation.executeResultWithRead]
    at produced
  change operation.executeWithRead input input.read = .ok outcomes at executed
  rw [executed] at produced
  simp only [bind, Except.bind, pure, Except.pure, Except.ok.injEq] at produced
  subst view
  exact ⟨rfl, rfl⟩

/-- Successful whole-call composition preserves the exact prepared Boolean result, including its eager findings and source-relative action partitions. -/
theorem addressedBooleanFirstFilled_executeResultWithFormalInputs_exact
    (operation : CheckedAddressedBooleanFirstFilledComputation model)
    (input : CheckedDocument model)
    (plan : CheckedComputationFormalInputPlan model)
    (prepared : ComputationFormalInputPreparation model)
    (result : AddressedBooleanFirstFilledComputationRunView model
      ComputationFormalInputFinding)
    (planned : operation.formalInputPlan = .ok plan)
    (preparation : plan.prepare input = .ok prepared)
    (executed : operation.executeResultWithRead input
      prepared.preliminary.readComputation
      prepared.formalErrorsInOperands = .ok result) :
    operation.executeResultWithFormalInputs input = .ok result := by
  rw [CheckedAddressedBooleanFirstFilledComputation.executeResultWithFormalInputs,
    planned]
  simp only [Except.mapError, bind, Except.bind, preparation, executed]

/-- A post-preparation execution failure retains the exact eager input findings beside the unchanged addressed Boolean fault. -/
theorem addressedBooleanFirstFilled_executeResultWithFormalInputs_failure_exact
    (operation : CheckedAddressedBooleanFirstFilledComputation model)
    (input : CheckedDocument model)
    (plan : CheckedComputationFormalInputPlan model)
    (prepared : ComputationFormalInputPreparation model)
    (fault : AddressedBooleanFirstFilledComputationFault)
    (planned : operation.formalInputPlan = .ok plan)
    (preparation : plan.prepare input = .ok prepared)
    (executed : operation.executeResultWithRead input
      prepared.preliminary.readComputation
      prepared.formalErrorsInOperands = .error fault) :
    operation.executeResultWithFormalInputs input =
      .error (.execution prepared.formalErrorsInOperands fault) := by
  rw [CheckedAddressedBooleanFirstFilledComputation.executeResultWithFormalInputs,
    planned]
  simp only [Except.mapError, bind, Except.bind, preparation, executed]

/-- Addressed application is exactly the common Boolean fold over a separately supplied document's exact target-state projection. -/
theorem addressedBooleanFirstFilledRun_applyToChecked_delegates
    (view : AddressedBooleanFirstFilledComputationRunView model ResidualMessage)
    (destination : CheckedDocument model) :
    view.applyToChecked destination =
      view.boolean.applyTo destination.sourceBooleanTargetStateAt := by
  rfl

end A12Kernel
