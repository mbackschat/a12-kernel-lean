import A12Kernel.Elaboration.DateFragmentFirstFilledComputation
import A12Kernel.Elaboration.AddressedDateFragmentFirstFilledComputation
import A12Kernel.Proofs.ExactTokenComputationResult
import A12Kernel.Proofs.StringComputationRunApplication

/-! # Direct and exact-address DateFragment `FirstFilledValue` computation laws -/

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

/-- Successful result construction retains the exact checked DateFragment operation. -/
theorem checkedDateFragmentFirstFilled_executeResult_operation
    (operation : CheckedDateFragmentFirstFilledComputation model)
    (input : CheckedDocument model) (residualMessages : List ResidualMessage)
    (selected : TokenComputationResult)
    (executed : operation.execute input = .ok selected)
    (view : DateFragmentFirstFilledComputationRunView model ResidualMessage)
    (produced : operation.executeResult input residualMessages = .ok view) :
    view.operation = operation := by
  rw [CheckedDateFragmentFirstFilledComputation.executeResult, executed] at produced
  cases produced
  rfl

/-- Exact-token DateFragment result construction cannot create a target-rejection channel. -/
theorem checkedDateFragmentFirstFilled_executeResult_hasNoTargetErrors
    (operation : CheckedDateFragmentFirstFilledComputation model)
    (input : CheckedDocument model) (residualMessages : List ResidualMessage)
    (selected : TokenComputationResult)
    (executed : operation.execute input = .ok selected)
    (view : DateFragmentFirstFilledComputationRunView model ResidualMessage)
    (produced : operation.executeResult input residualMessages = .ok view) :
    view.string.withErrors = [] := by
  rw [CheckedDateFragmentFirstFilledComputation.executeResult, executed] at produced
  cases produced
  apply exactTokenStringResult_hasNoTargetErrors

/-- Every retained DateFragment action names the checked operation's exact target. -/
theorem checkedDateFragmentFirstFilled_executeResult_actionsOwned
    (operation : CheckedDateFragmentFirstFilledComputation model)
    (input : CheckedDocument model) (residualMessages : List ResidualMessage)
    (selected : TokenComputationResult)
    (executed : operation.execute input = .ok selected)
    (view : DateFragmentFirstFilledComputationRunView model ResidualMessage)
    (produced : operation.executeResult input residualMessages = .ok view) :
    view.string.actionTargets.all (· == operation.targetField) = true := by
  rw [CheckedDateFragmentFirstFilledComputation.executeResult, executed] at produced
  cases produced
  apply oneTargetStringResult_actionsOwned

/-- Same-model DateFragment application delegates exactly to the established source-classified text fold over the separately supplied destination. -/
theorem dateFragmentFirstFilled_applyToChecked_delegates
    (view : DateFragmentFirstFilledComputationRunView model ResidualMessage)
    (destination : CheckedDocument model) :
    view.applyToChecked destination =
      view.string.applyTo destination.sourceStringTargetState := by
  rfl

/-- The addressed source and target retain one exact DateFragment carrier and the shared bounded sibling-star placement. -/
theorem checkedAddressedDateFragmentFirstFilled_source_bounded
    (operation : CheckedAddressedDateFragmentFirstFilledComputation model) :
    operation.carrier.isDateFragment = true ∧
      operation.target.temporalFirstFilledStarCarrier? =
        some operation.carrier ∧
      operation.source.declaration.temporalFirstFilledStarCarrier? =
        some operation.carrier ∧
      operation.source.reopenedScope.length = 1 ∧
      operation.source.bindingScope ≠ [] ∧
      operation.source.bindingScope.all
        operation.target.repeatableScope.contains = true :=
  ⟨operation.carrierIsFragment, operation.targetCarrier,
    operation.sourceCarrier,
    operation.placement.sourceSingleReopenedAxis,
    operation.placement.sourceBindingNonempty,
    operation.placement.sourceBindingBound⟩

/-- Addressed result construction retains the checked operation and classifies every outcome against its exact immutable target state. -/
theorem checkedAddressedDateFragmentFirstFilled_executeResult_projects
    (operation : CheckedAddressedDateFragmentFirstFilledComputation model)
    (input : CheckedDocument model) (messages : List ResidualMessage)
    (outcomes : List AddressedDateFragmentFirstFilledComputationOutcome)
    (view : AddressedDateFragmentFirstFilledComputationRunView
      model ResidualMessage)
    (executed : operation.execute input = .ok outcomes)
    (produced : operation.executeResult input messages = .ok view) :
    view.operation = operation ∧
      view.string = projectAddressedTokenResults input messages outcomes := by
  rw [CheckedAddressedDateFragmentFirstFilledComputation.executeResult,
    executed] at produced
  simp only [bind, Except.bind, pure, Except.pure, Except.ok.injEq] at produced
  subst view
  exact ⟨rfl, rfl⟩

/-- Exact-token addressed DateFragment selection cannot create an ordinary String target-rejection channel. -/
theorem checkedAddressedDateFragmentFirstFilled_executeResult_hasNoTargetErrors
    (operation : CheckedAddressedDateFragmentFirstFilledComputation model)
    (input : CheckedDocument model) (messages : List ResidualMessage)
    (outcomes : List AddressedDateFragmentFirstFilledComputationOutcome)
    (executed : operation.execute input = .ok outcomes) :
    (operation.executeResult input messages).map
      (fun view => view.string.withErrors) = .ok [] := by
  unfold CheckedAddressedDateFragmentFirstFilledComputation.executeResult
  rw [executed]
  change Except.ok
    ((projectAddressedTokenResults input messages outcomes).withErrors) =
      Except.ok []
  exact congrArg Except.ok
    (addressedTokenResults_haveNoTargetErrors outcomes input messages)

/-- Exact-address checked application delegates to the established source-classified String fold. -/
theorem addressedDateFragmentFirstFilledRun_applyToChecked_delegates
    (view : AddressedDateFragmentFirstFilledComputationRunView
      model ResidualMessage)
    (destination : CheckedDocument model) :
    view.applyToChecked destination =
      view.string.applyTo destination.sourceStringTargetStateAt := by
  rfl

end A12Kernel
