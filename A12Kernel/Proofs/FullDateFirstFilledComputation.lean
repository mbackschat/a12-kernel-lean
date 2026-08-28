import A12Kernel.Elaboration.FullDateFirstFilledComputation
import A12Kernel.Elaboration.AddressedFullDateFirstFilledFormalInput

/-! # Direct and exact-address full-Date `FirstFilledValue` computation laws -/

namespace A12Kernel

/-- A clean checked full-Date value retains exact instant identity before target rendering. -/
theorem fullDateFirstFilledCellAt_value
    (addressed : CheckedAddressedCell) (date : DateValue)
    (observed : observeCell .computation addressed.cell =
      .value (.temporal (.date date))) :
    fullDateFirstFilledCellAt addressed = .value date.instant := by
  simp [fullDateFirstFilledCellAt, observed]

/-- A reached formal rejection retains its exact cause at the full-Date selection boundary. -/
theorem fullDateFirstFilledCellAt_poison
    (addressed : CheckedAddressedCell) (cause : FormalCause)
    (observed : observeCell .computation addressed.cell = .poison cause) :
    fullDateFirstFilledCellAt addressed = .poison cause := by
  simp [fullDateFirstFilledCellAt, observed]

/-- A present head terminates the full-Date scan before every suffix cell. -/
theorem evalFullDateFirstFilledCells_present_head
    (addressed : CheckedAddressedCell) (remaining : List CheckedAddressedCell)
    (instant : Instant)
    (selected : fullDateFirstFilledCellAt addressed = .value instant) :
    evalFullDateFirstFilledCells (addressed :: remaining) = .value instant := by
  simp [evalFullDateFirstFilledCells, selected]

/-- A formally unavailable head terminates the full-Date scan before every suffix cell. -/
theorem evalFullDateFirstFilledCells_poison_head
    (addressed : CheckedAddressedCell) (remaining : List CheckedAddressedCell)
    (cause : FormalCause)
    (selected : fullDateFirstFilledCellAt addressed = .poison cause) :
    evalFullDateFirstFilledCells (addressed :: remaining) = .poison cause := by
  simp [evalFullDateFirstFilledCells, selected]

/-- Result construction retains the operation-owned target and delegates every public projection to the established FullDate outcome classifier. -/
theorem fullDateFirstFilled_executeResult_projects
    (operation : CheckedFullDateFirstFilledComputation model)
    (input : CheckedDocument model)
    (residualMessages : List ResidualMessage)
    (outcome : FullDateTargetOutcome)
    (evaluated : operation.execute input = .ok outcome) :
    operation.executeResult input residualMessages =
      .ok (FullDateComputationRunView.fromOutcomes input residualMessages
        [(operation.targetPolicy.checked.target.id, outcome)]) := by
  rw [CheckedFullDateFirstFilledComputation.executeResult, evaluated]
  rfl

/-- The immutable addressed executor is definitionally the caller-read route specialized to the document's checked read. -/
theorem addressedFullDateFirstFilled_executeWithRead_base
    (operation : CheckedAddressedFullDateFirstFilledComputation model)
    (input : CheckedDocument model) :
    operation.executeWithRead input input.read = operation.execute input := by
  rfl

/-- Addressed result construction retains the checked operation and classifies every executed outcome under its exact target address. -/
theorem addressedFullDateFirstFilled_executeResult_projects
    (operation : CheckedAddressedFullDateFirstFilledComputation model)
    (input : CheckedDocument model) (messages : List ResidualMessage)
    (outcomes : List AddressedFullDateFirstFilledComputationOutcome)
    (view : AddressedFullDateFirstFilledComputationRunView model ResidualMessage)
    (executed : operation.execute input = .ok outcomes)
    (produced : operation.executeResult input messages = .ok view) :
    view.operation = operation ∧
      view.fullDate = FullDateComputationRunView.fromOutcomesAt
        input.sourceFullDateTargetStateAt messages
        (outcomes.map fun entry => (entry.targetField, entry.outcome)) := by
  rw [CheckedAddressedFullDateFirstFilledComputation.executeResult,
    CheckedAddressedFullDateFirstFilledComputation.executeResultWithRead]
    at produced
  change operation.executeWithRead input input.read = .ok outcomes at executed
  rw [executed] at produced
  simp only [bind, Except.bind, pure, Except.pure, Except.ok.injEq] at produced
  subst view
  exact ⟨rfl, rfl⟩

/-- Successful whole-call composition preserves the exact prepared FULL Date result, including its eager findings, target rendering, and source-relative actions. -/
theorem addressedFullDateFirstFilled_executeResultWithFormalInputs_exact
    (operation : CheckedAddressedFullDateFirstFilledComputation model)
    (input : CheckedDocument model)
    (plan : CheckedComputationFormalInputPlan model)
    (prepared : ComputationFormalInputPreparation model)
    (result : AddressedFullDateFirstFilledComputationRunView model
      ComputationFormalInputFinding)
    (planned : operation.formalInputPlan = .ok plan)
    (preparation : plan.prepare input = .ok prepared)
    (executed : operation.executeResultWithRead input
      prepared.preliminary.readComputation
      prepared.formalErrorsInOperands = .ok result) :
    operation.executeResultWithFormalInputs input = .ok result := by
  rw [CheckedAddressedFullDateFirstFilledComputation.executeResultWithFormalInputs,
    planned]
  simp only [Except.mapError, bind, Except.bind, preparation, executed]

/-- A post-preparation execution failure retains the exact eager input findings beside the unchanged addressed FULL Date fault. -/
theorem addressedFullDateFirstFilled_executeResultWithFormalInputs_failure_exact
    (operation : CheckedAddressedFullDateFirstFilledComputation model)
    (input : CheckedDocument model)
    (plan : CheckedComputationFormalInputPlan model)
    (prepared : ComputationFormalInputPreparation model)
    (fault : AddressedFullDateFirstFilledComputationFault)
    (planned : operation.formalInputPlan = .ok plan)
    (preparation : plan.prepare input = .ok prepared)
    (executed : operation.executeResultWithRead input
      prepared.preliminary.readComputation
      prepared.formalErrorsInOperands = .error fault) :
    operation.executeResultWithFormalInputs input =
      .error (.execution prepared.formalErrorsInOperands fault) := by
  rw [CheckedAddressedFullDateFirstFilledComputation.executeResultWithFormalInputs,
    planned]
  simp only [Except.mapError, bind, Except.bind, preparation, executed]

/-- Addressed application is exactly the common FullDate fold over the separately supplied document's exact cell-state projection. -/
theorem addressedFullDateFirstFilledRun_applyToChecked_delegates
    (view : AddressedFullDateFirstFilledComputationRunView model ResidualMessage)
    (destination : CheckedDocument model) :
    view.applyToChecked destination =
      view.fullDate.applyTo destination.sourceFullDateTargetStateAt := by
  rfl

end A12Kernel
