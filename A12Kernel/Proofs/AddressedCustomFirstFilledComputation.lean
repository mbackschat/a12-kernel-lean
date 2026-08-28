import A12Kernel.Elaboration.AddressedCustomFirstFilledFormalInput
import A12Kernel.Proofs.ExactTokenComputationResult

/-! # Exact-address repeatable Custom `FirstFilledValue` laws -/

namespace A12Kernel

/-- The checked source carries the target's Custom declaration and has one reopened star axis with a nonempty outer prefix supplied by the target scope. -/
theorem checkedAddressedCustomFirstFilled_source_bounded
    (operation : CheckedAddressedCustomFirstFilledComputation model) :
    operation.target.customType = some operation.customType ∧
      operation.source.declaration.customType = some operation.customType ∧
      operation.source.reopenedScope.length = 1 ∧
      operation.source.bindingScope ≠ [] ∧
      operation.source.bindingScope.all
        operation.target.repeatableScope.contains = true :=
  ⟨operation.targetCustom, operation.sourceCustom,
    operation.sourceSingleReopenedAxis, operation.sourceBindingNonempty,
    operation.sourceBindingBound⟩

/-- The immutable addressed executor is definitionally the caller-read route specialized to the document's checked read. -/
theorem checkedAddressedCustomFirstFilled_executeWithRead_base
    (operation : CheckedAddressedCustomFirstFilledComputation model)
    (input : CheckedDocument model) :
    operation.executeWithRead input input.read = operation.execute input := by
  rfl

/-- Addressed result construction retains the checked operation and classifies every outcome against its exact immutable target state. -/
theorem checkedAddressedCustomFirstFilled_executeResult_projects
    (operation : CheckedAddressedCustomFirstFilledComputation model)
    (input : CheckedDocument model) (messages : List ResidualMessage)
    (outcomes : List AddressedCustomFirstFilledComputationOutcome)
    (view : AddressedCustomFirstFilledComputationRunView model ResidualMessage)
    (executed : operation.execute input = .ok outcomes)
    (produced : operation.executeResult input messages = .ok view) :
    view.operation = operation ∧
      view.string = projectAddressedTokenResults input messages outcomes := by
  rw [CheckedAddressedCustomFirstFilledComputation.executeResult,
    CheckedAddressedCustomFirstFilledComputation.executeResultWithRead]
    at produced
  change operation.executeWithRead input input.read = .ok outcomes at executed
  rw [executed] at produced
  simp only [bind, Except.bind, pure, Except.pure, Except.ok.injEq] at produced
  subst view
  exact ⟨rfl, rfl⟩

/-- Exact-token Custom selection cannot create an ordinary String target-rejection channel. -/
theorem checkedAddressedCustomFirstFilled_executeResult_hasNoTargetErrors
    (operation : CheckedAddressedCustomFirstFilledComputation model)
    (input : CheckedDocument model) (messages : List ResidualMessage)
    (outcomes : List AddressedCustomFirstFilledComputationOutcome)
    (executed : operation.execute input = .ok outcomes) :
    (operation.executeResult input messages).map
      (fun view => view.string.withErrors) = .ok [] := by
  rw [CheckedAddressedCustomFirstFilledComputation.executeResult,
    CheckedAddressedCustomFirstFilledComputation.executeResultWithRead]
  change operation.executeWithRead input input.read = .ok outcomes at executed
  rw [executed]
  change Except.ok
    ((projectAddressedTokenResults input messages outcomes).withErrors) =
      Except.ok []
  exact congrArg Except.ok
    (addressedTokenResults_haveNoTargetErrors outcomes input messages)

/-- Successful whole-call composition preserves the exact prepared Custom result, including eager findings and source-relative actions. -/
theorem checkedAddressedCustomFirstFilled_executeResultWithFormalInputs_exact
    (operation : CheckedAddressedCustomFirstFilledComputation model)
    (input : CheckedDocument model)
    (plan : CheckedComputationFormalInputPlan model)
    (prepared : ComputationFormalInputPreparation model)
    (result : AddressedCustomFirstFilledComputationRunView model
      ComputationFormalInputFinding)
    (planned : operation.formalInputPlan = .ok plan)
    (preparation : plan.prepare input = .ok prepared)
    (executed : operation.executeResultWithRead input
      prepared.preliminary.readComputation
      prepared.formalErrorsInOperands = .ok result) :
    operation.executeResultWithFormalInputs input = .ok result := by
  rw [CheckedAddressedCustomFirstFilledComputation.executeResultWithFormalInputs,
    planned]
  simp only [Except.mapError, bind, Except.bind, preparation, executed]

/-- A post-preparation execution failure retains the exact eager input findings beside the unchanged addressed Custom fault. -/
theorem checkedAddressedCustomFirstFilled_executeResultWithFormalInputs_failure_exact
    (operation : CheckedAddressedCustomFirstFilledComputation model)
    (input : CheckedDocument model)
    (plan : CheckedComputationFormalInputPlan model)
    (prepared : ComputationFormalInputPreparation model)
    (fault : AddressedCustomFirstFilledComputationFault)
    (planned : operation.formalInputPlan = .ok plan)
    (preparation : plan.prepare input = .ok prepared)
    (executed : operation.executeResultWithRead input
      prepared.preliminary.readComputation
      prepared.formalErrorsInOperands = .error fault) :
    operation.executeResultWithFormalInputs input =
      .error (.execution prepared.formalErrorsInOperands fault) := by
  rw [CheckedAddressedCustomFirstFilledComputation.executeResultWithFormalInputs,
    planned]
  simp only [Except.mapError, bind, Except.bind, preparation, executed]

/-- Exact-address checked application delegates to the established source-classified String fold. -/
theorem addressedCustomFirstFilledRun_applyToChecked_delegates
    (view : AddressedCustomFirstFilledComputationRunView model ResidualMessage)
    (destination : CheckedDocument model) :
    view.applyToChecked destination =
      view.string.applyTo destination.sourceStringTargetStateAt := by
  rfl

end A12Kernel
