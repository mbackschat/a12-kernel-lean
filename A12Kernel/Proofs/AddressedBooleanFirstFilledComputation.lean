import A12Kernel.Elaboration.AddressedBooleanFirstFilledComputation

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
  rw [CheckedAddressedBooleanFirstFilledComputation.executeResult, executed]
    at produced
  simp only [bind, Except.bind, pure, Except.pure, Except.ok.injEq] at produced
  subst view
  exact ⟨rfl, rfl⟩

/-- Addressed application is exactly the common Boolean fold over a separately supplied document's exact target-state projection. -/
theorem addressedBooleanFirstFilledRun_applyToChecked_delegates
    (view : AddressedBooleanFirstFilledComputationRunView model ResidualMessage)
    (destination : CheckedDocument model) :
    view.applyToChecked destination =
      view.boolean.applyTo destination.sourceBooleanTargetStateAt := by
  rfl

end A12Kernel
