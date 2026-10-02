import A12Kernel.Elaboration.DateFragmentFirstFilledComputation
import A12Kernel.Proofs.ExactTokenComputationResult
import A12Kernel.Proofs.StringComputationRunApplication

/-! # DateFragment `FirstFilledValue` laws at a fixed or a repeatable target -/

namespace A12Kernel

/-- A clean checked DateFragment value retains the token presented to the bounded first-filled adapter. -/
theorem dateFragmentFirstFilledCellAt_value
    (addressed : CheckedAddressedCell) (date : DateValue) (token : String)
    (observed : observeCell .computation addressed.cell =
      .value (.temporal (.date date)))
    (stored : addressed.stored = some token) :
    dateFragmentFirstFilledCellAt addressed = .present token := by
  simp [dateFragmentFirstFilledCellAt, observed, stored]

/-- A reached formal rejection retains its exact cause at the DateFragment computation adapter. -/
theorem dateFragmentFirstFilledCellAt_poison
    (addressed : CheckedAddressedCell) (cause : FormalCause)
    (observed : observeCell .computation addressed.cell = .poison cause) :
    dateFragmentFirstFilledCellAt addressed = .unknown cause := by
  simp [dateFragmentFirstFilledCellAt, observed]

/-- The checked operation retains one exact fragment profile on the target and every source
declaration, and a source that cannot read its target. -/
theorem checkedDateFragmentFirstFilled_carriers
    (operation : CheckedDateFragmentFirstFilledComputation model) :
    operation.shape.carrier.isDateFragment = true ∧
      (operation.target.firstFilledTargetProfile operation.shape.ownsBefore1900
        ).temporalFirstFilledStarCarrier? = some operation.shape.carrier ∧
      operation.shape.site.source.declarations.all
        (·.temporalFirstFilledStarCarrier? == some operation.shape.sourceProfile) = true ∧
      operation.shape.carrier.acceptsSource operation.shape.sourceProfile = true ∧
      operation.referencesField operation.targetField = false :=
  ⟨operation.fragment, operation.shape.targetCarrier, operation.shape.sourceCarrier,
    operation.shape.sourceAccepted, operation.excludesTarget⟩

/-- The immutable-document executor is definitionally the caller-read route specialized to the
document's checked read. -/
theorem checkedDateFragmentFirstFilled_executeWithRead_base
    (operation : CheckedDateFragmentFirstFilledComputation model)
    (input : CheckedDocument model) :
    operation.executeWithRead input input.read = operation.execute input := by
  rfl

/-- Result construction retains the checked operation and classifies every outcome against its exact
immutable target state. -/
theorem checkedDateFragmentFirstFilled_executeResult_projects
    (operation : CheckedDateFragmentFirstFilledComputation model)
    (input : CheckedDocument model) (messages : List ResidualMessage)
    (outcomes : List AddressedTokenComputationOutcome)
    (view : DateFragmentFirstFilledComputationRunView model ResidualMessage)
    (executed : operation.execute input = .ok outcomes)
    (produced : operation.executeResult input messages = .ok view) :
    view.operation = operation ∧
      view.string = projectAddressedTokenResults input messages outcomes := by
  rw [CheckedDateFragmentFirstFilledComputation.executeResult,
    CheckedDateFragmentFirstFilledComputation.executeResultWithRead] at produced
  change operation.executeWithRead input input.read = .ok outcomes at executed
  rw [executed] at produced
  simp only [bind, Except.bind, pure, Except.pure, Except.ok.injEq] at produced
  subst view
  exact ⟨rfl, rfl⟩

/-- Exact-token DateFragment selection cannot create an ordinary String target-rejection channel. -/
theorem checkedDateFragmentFirstFilled_executeResult_hasNoTargetErrors
    (operation : CheckedDateFragmentFirstFilledComputation model)
    (input : CheckedDocument model) (messages : List ResidualMessage)
    (outcomes : List AddressedTokenComputationOutcome)
    (executed : operation.execute input = .ok outcomes) :
    (operation.executeResult input messages).map
      (fun view => view.string.withErrors) = .ok [] := by
  unfold CheckedDateFragmentFirstFilledComputation.executeResult
    CheckedDateFragmentFirstFilledComputation.executeResultWithRead
  change operation.executeWithRead input input.read = .ok outcomes at executed
  rw [executed]
  change Except.ok
    ((projectAddressedTokenResults input messages outcomes).withErrors) =
      Except.ok []
  exact congrArg Except.ok
    (addressedTokenResults_haveNoTargetErrors outcomes input messages)

/-- Successful whole-call composition preserves the exact prepared DateFragment result, including
its eager findings and exact token/action partitions. -/
theorem checkedDateFragmentFirstFilled_executeResultWithFormalInputs_exact
    (operation : CheckedDateFragmentFirstFilledComputation model)
    (input : CheckedDocument model)
    (plan : CheckedComputationFormalInputPlan model)
    (prepared : ComputationFormalInputPreparation model)
    (result : DateFragmentFirstFilledComputationRunView model ComputationFormalInputFinding)
    (planned : operation.formalInputPlan = .ok plan)
    (preparation : plan.prepare input = .ok prepared)
    (executed : operation.executeResultWithRead input prepared.preliminary.readComputation
      prepared.formalErrorsInOperands = .ok result) :
    operation.executeResultWithFormalInputs input = .ok result := by
  rw [CheckedDateFragmentFirstFilledComputation.executeResultWithFormalInputs, planned]
  simp only [Except.mapError, bind, Except.bind, preparation, executed]

/-- A post-preparation execution failure retains the exact eager input findings beside the unchanged
DateFragment fault. -/
theorem checkedDateFragmentFirstFilled_executeResultWithFormalInputs_failure_exact
    (operation : CheckedDateFragmentFirstFilledComputation model)
    (input : CheckedDocument model)
    (plan : CheckedComputationFormalInputPlan model)
    (prepared : ComputationFormalInputPreparation model)
    (fault : FirstFilledSiteFault)
    (planned : operation.formalInputPlan = .ok plan)
    (preparation : plan.prepare input = .ok prepared)
    (executed : operation.executeResultWithRead input prepared.preliminary.readComputation
      prepared.formalErrorsInOperands = .error fault) :
    operation.executeResultWithFormalInputs input =
      .error (.execution prepared.formalErrorsInOperands fault) := by
  rw [CheckedDateFragmentFirstFilledComputation.executeResultWithFormalInputs, planned]
  simp only [Except.mapError, bind, Except.bind, preparation, executed]

/-- Checked application delegates to the established source-classified String fold. -/
theorem dateFragmentFirstFilled_applyToChecked_delegates
    (view : DateFragmentFirstFilledComputationRunView model ResidualMessage)
    (destination : CheckedDocument model) :
    view.applyToChecked destination =
      view.string.applyTo destination.sourceStringTargetStateAt := by
  rfl

end A12Kernel
