import A12Kernel.Elaboration.AddressedStringFirstFilledFormalInput
import A12Kernel.Proofs.StringComputationRunApplication

/-! # Exact-address repeatable ordinary String `FirstFilledValue` laws -/

namespace A12Kernel

/-- The checked operation retains ordinary String carriers and one sibling-star axis whose nonempty binding prefix is supplied by the target scope. -/
theorem checkedAddressedStringFirstFilled_carriersAndPlacement
    (operation : CheckedAddressedStringFirstFilledComputation model) :
    operation.target.isOrdinaryStringComputationCarrier = true ∧
      operation.source.declaration.isOrdinaryStringComputationCarrier = true ∧
      operation.source.reopenedScope.length = 1 ∧
      operation.source.bindingScope ≠ [] ∧
      operation.source.bindingScope.isPrefixOf
        operation.target.repeatableScope = true ∧
      operation.source.bindingScope ≠ operation.target.repeatableScope ∧ operation.source.declaration.id ≠ operation.targetField ∧
      operation.source.bindingScope.all
        operation.target.repeatableScope.contains = true :=
  ⟨operation.targetOrdinary, operation.sourceOrdinary,
    operation.placement.sourceSingleReopenedAxis,
    operation.placement.sourceBindingNonempty,
    operation.sourceBindingPrefix, operation.sourceBindingStrict, operation.placement.targetNotReferenced,
    operation.placement.sourceBindingBound⟩

/-- The immutable addressed executor is definitionally the caller-read route specialized to the document's checked read. -/
theorem checkedAddressedStringFirstFilled_executeWithRead_base
    (operation : CheckedAddressedStringFirstFilledComputation model)
    (patterns : PreparedFlatStringPatterns model compilePattern)
    (input : CheckedDocument model) :
    operation.executeWithRead patterns input input.read =
      operation.execute patterns input := by
  rfl

/-- Addressed result construction retains the checked operation and classifies every outcome against its exact immutable target state. -/
theorem checkedAddressedStringFirstFilled_executeResult_projects
    (operation : CheckedAddressedStringFirstFilledComputation model)
    (patterns : PreparedFlatStringPatterns model compilePattern)
    (input : CheckedDocument model) (messages : List ResidualMessage)
    (outcomes : List AddressedStringFirstFilledComputationOutcome)
    (view : AddressedStringFirstFilledComputationRunView model ResidualMessage)
    (executed : operation.execute patterns input = .ok outcomes)
    (produced : operation.executeResult patterns input messages = .ok view) :
    view.operation = operation ∧
      view.string = StringComputationRunView.fromSourcedOutcomes messages
        (outcomes.map fun entry => {
          targetField := entry.targetField
          outcome := entry.outcome
          source := input.sourceStringTargetStateAt entry.targetField
        }) := by
  rw [CheckedAddressedStringFirstFilledComputation.executeResult,
    CheckedAddressedStringFirstFilledComputation.executeResultWithRead]
    at produced
  change operation.executeWithRead patterns input input.read = .ok outcomes
    at executed
  rw [executed] at produced
  simp only [bind, Except.bind, pure, Except.pure, Except.ok.injEq] at produced
  subst view
  exact ⟨rfl, rfl⟩

/-- Successful whole-call composition preserves the exact prepared String result, including eager findings, target-policy outcomes, and source-relative actions. -/
theorem checkedAddressedStringFirstFilled_executeResultWithFormalInputs_exact
    (operation : CheckedAddressedStringFirstFilledComputation model)
    (patterns : PreparedFlatStringPatterns model compilePattern)
    (input : CheckedDocument model)
    (plan : CheckedComputationFormalInputPlan model)
    (prepared : ComputationFormalInputPreparation model)
    (result : AddressedStringFirstFilledComputationRunView model
      ComputationFormalInputFinding)
    (planned : operation.formalInputPlan = .ok plan)
    (preparation : plan.prepare input = .ok prepared)
    (executed : operation.executeResultWithRead patterns input
      prepared.preliminary.readComputation
      prepared.formalErrorsInOperands = .ok result) :
    operation.executeResultWithFormalInputs patterns input = .ok result := by
  rw [CheckedAddressedStringFirstFilledComputation.executeResultWithFormalInputs,
    planned]
  simp only [Except.mapError, bind, Except.bind, preparation, executed]

/-- A post-preparation execution failure retains the exact eager input findings beside the unchanged addressed String fault. -/
theorem checkedAddressedStringFirstFilled_executeResultWithFormalInputs_failure_exact
    (operation : CheckedAddressedStringFirstFilledComputation model)
    (patterns : PreparedFlatStringPatterns model compilePattern)
    (input : CheckedDocument model)
    (plan : CheckedComputationFormalInputPlan model)
    (prepared : ComputationFormalInputPreparation model)
    (fault : AddressedStringFirstFilledComputationFault)
    (planned : operation.formalInputPlan = .ok plan)
    (preparation : plan.prepare input = .ok prepared)
    (executed : operation.executeResultWithRead patterns input
      prepared.preliminary.readComputation
      prepared.formalErrorsInOperands = .error fault) :
    operation.executeResultWithFormalInputs patterns input =
      .error (.execution prepared.formalErrorsInOperands fault) := by
  rw [CheckedAddressedStringFirstFilledComputation.executeResultWithFormalInputs,
    planned]
  simp only [Except.mapError, bind, Except.bind, preparation, executed]

/-- Exact-address checked application delegates to the established source-classified String fold. -/
theorem addressedStringFirstFilledRun_applyToChecked_delegates
    (view : AddressedStringFirstFilledComputationRunView model ResidualMessage)
    (destination : CheckedDocument model) :
    view.applyToChecked destination =
      view.string.applyTo destination.sourceStringTargetStateAt := by
  rfl

end A12Kernel
