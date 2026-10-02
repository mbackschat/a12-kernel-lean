import A12Kernel.Elaboration.CustomFirstFilledComputation
import A12Kernel.Proofs.ExactTokenComputationResult
import A12Kernel.Proofs.StringComputationRunApplication

/-! # Custom `FirstFilledValue` laws at a fixed or a repeatable target -/

namespace A12Kernel

/-- A clean prepared Custom String remains the exact token consumed by the shared first-filled scan. -/
theorem customFirstFilledCellAt_value (value : String) :
    customFirstFilledCellAt {
      rawPresent := true, parsed := some (.str value), findings := []
    } = .present value := by
  rfl

/-- A registered Custom rejection retains its exact cause at the computation adapter. -/
theorem customFirstFilledCellAt_registeredRejection
    (value : String) (rejection : RegisteredCustomRejection) :
    customFirstFilledCellAt {
      rawPresent := true
      parsed := some (.str value)
      findings := [.registeredCustomValidation rejection]
    } = .unknown (.registeredCustomValidation rejection) := by
  rfl

/-- The checked operation retains one Custom declaration on the target and every source
declaration, and a source that cannot read its target. -/
theorem checkedCustomFirstFilled_carriers (operation : CheckedCustomFirstFilledComputation model) :
    operation.target.customType = some operation.customType ∧
      operation.site.source.declarations.all (·.customType == some operation.customType) = true ∧
      operation.referencesField operation.targetField = false :=
  ⟨operation.targetCustom, operation.sourceCustom, operation.excludesTarget⟩

/-- The immutable addressed executor is definitionally the caller-read route specialized to the document's checked read. -/
theorem checkedCustomFirstFilled_executeWithRead_base
    (operation : CheckedCustomFirstFilledComputation model)
    (input : CheckedDocument model) :
    operation.executeWithRead input input.read = operation.execute input := by
  rfl

/-- Result construction retains the checked operation and classifies every outcome against its exact immutable target state. -/
theorem checkedCustomFirstFilled_executeResult_projects
    (operation : CheckedCustomFirstFilledComputation model)
    (input : CheckedDocument model) (messages : List ResidualMessage)
    (outcomes : List AddressedTokenComputationOutcome)
    (view : CustomFirstFilledComputationRunView model ResidualMessage)
    (executed : operation.execute input = .ok outcomes)
    (produced : operation.executeResult input messages = .ok view) :
    view.operation = operation ∧
      view.string = projectAddressedTokenResults input messages outcomes := by
  rw [CheckedCustomFirstFilledComputation.executeResult,
    CheckedCustomFirstFilledComputation.executeResultWithRead]
    at produced
  change operation.executeWithRead input input.read = .ok outcomes at executed
  rw [executed] at produced
  simp only [bind, Except.bind, pure, Except.pure, Except.ok.injEq] at produced
  subst view
  exact ⟨rfl, rfl⟩

/-- Exact-token Custom selection cannot create an ordinary String target-rejection channel. -/
theorem checkedCustomFirstFilled_executeResult_hasNoTargetErrors
    (operation : CheckedCustomFirstFilledComputation model)
    (input : CheckedDocument model) (messages : List ResidualMessage)
    (outcomes : List AddressedTokenComputationOutcome)
    (executed : operation.execute input = .ok outcomes) :
    (operation.executeResult input messages).map
      (fun view => view.string.withErrors) = .ok [] := by
  rw [CheckedCustomFirstFilledComputation.executeResult,
    CheckedCustomFirstFilledComputation.executeResultWithRead]
  change operation.executeWithRead input input.read = .ok outcomes at executed
  rw [executed]
  change Except.ok
    ((projectAddressedTokenResults input messages outcomes).withErrors) =
      Except.ok []
  exact congrArg Except.ok
    (addressedTokenResults_haveNoTargetErrors outcomes input messages)

/-- Successful whole-call composition preserves the exact prepared Custom result, including eager findings and source-relative actions. -/
theorem checkedCustomFirstFilled_executeResultWithFormalInputs_exact
    (operation : CheckedCustomFirstFilledComputation model)
    (input : CheckedDocument model)
    (plan : CheckedComputationFormalInputPlan model)
    (prepared : ComputationFormalInputPreparation model)
    (result : CustomFirstFilledComputationRunView model
      ComputationFormalInputFinding)
    (planned : operation.formalInputPlan = .ok plan)
    (preparation : plan.prepare input = .ok prepared)
    (executed : operation.executeResultWithRead input
      prepared.preliminary.readComputation
      prepared.formalErrorsInOperands = .ok result) :
    operation.executeResultWithFormalInputs input = .ok result := by
  rw [CheckedCustomFirstFilledComputation.executeResultWithFormalInputs,
    planned]
  simp only [Except.mapError, bind, Except.bind, preparation, executed]

/-- A post-preparation execution failure retains the exact eager input findings beside the unchanged Custom fault. -/
theorem checkedCustomFirstFilled_executeResultWithFormalInputs_failure_exact
    (operation : CheckedCustomFirstFilledComputation model)
    (input : CheckedDocument model)
    (plan : CheckedComputationFormalInputPlan model)
    (prepared : ComputationFormalInputPreparation model)
    (fault : FirstFilledSiteFault)
    (planned : operation.formalInputPlan = .ok plan)
    (preparation : plan.prepare input = .ok prepared)
    (executed : operation.executeResultWithRead input
      prepared.preliminary.readComputation
      prepared.formalErrorsInOperands = .error fault) :
    operation.executeResultWithFormalInputs input =
      .error (.execution prepared.formalErrorsInOperands fault) := by
  rw [CheckedCustomFirstFilledComputation.executeResultWithFormalInputs,
    planned]
  simp only [Except.mapError, bind, Except.bind, preparation, executed]

/-- Checked application delegates to the established source-classified String fold. -/
theorem customFirstFilledRun_applyToChecked_delegates
    (view : CustomFirstFilledComputationRunView model ResidualMessage)
    (destination : CheckedDocument model) :
    view.applyToChecked destination =
      view.string.applyTo destination.sourceStringTargetStateAt := by
  rfl

end A12Kernel
