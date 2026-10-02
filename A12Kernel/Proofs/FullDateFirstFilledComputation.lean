import A12Kernel.Elaboration.FullDateFirstFilledComputation

/-! # Full-Date `FirstFilledValue` laws at a fixed or a repeatable target -/

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

/-- The immutable-document executor is definitionally the caller-read route specialized to the document's checked read. -/
theorem checkedFullDateFirstFilled_executeWithRead_base
    (operation : CheckedFullDateFirstFilledComputation model)
    (input : CheckedDocument model) :
    operation.executeWithRead input input.read = operation.execute input := by
  rfl

/-- Result construction retains the checked operation and classifies every executed outcome under its exact target address. -/
theorem checkedFullDateFirstFilled_executeResult_projects
    (operation : CheckedFullDateFirstFilledComputation model)
    (input : CheckedDocument model) (messages : List ResidualMessage)
    (outcomes : List FullDateFirstFilledComputationOutcome)
    (view : FullDateFirstFilledComputationRunView model ResidualMessage)
    (executed : operation.execute input = .ok outcomes)
    (produced : operation.executeResult input messages = .ok view) :
    view.operation = operation ∧
      view.fullDate = FullDateComputationRunView.fromOutcomesAt
        input.sourceFullDateTargetStateAt messages
        (outcomes.map fun entry => (entry.targetField, entry.outcome)) := by
  rw [CheckedFullDateFirstFilledComputation.executeResult,
    CheckedFullDateFirstFilledComputation.executeResultWithRead]
    at produced
  change operation.executeWithRead input input.read = .ok outcomes at executed
  rw [executed] at produced
  simp only [bind, Except.bind, pure, Except.pure, Except.ok.injEq] at produced
  subst view
  exact ⟨rfl, rfl⟩

/-- Successful whole-call composition preserves the exact prepared FULL Date result, including its eager findings, target rendering, and source-relative actions. -/
theorem checkedFullDateFirstFilled_executeResultWithFormalInputs_exact
    (operation : CheckedFullDateFirstFilledComputation model)
    (input : CheckedDocument model)
    (plan : CheckedComputationFormalInputPlan model)
    (prepared : ComputationFormalInputPreparation model)
    (result : FullDateFirstFilledComputationRunView model
      ComputationFormalInputFinding)
    (planned : operation.formalInputPlan = .ok plan)
    (preparation : plan.prepare input = .ok prepared)
    (executed : operation.executeResultWithRead input
      prepared.preliminary.readComputation
      prepared.formalErrorsInOperands = .ok result) :
    operation.executeResultWithFormalInputs input = .ok result := by
  rw [CheckedFullDateFirstFilledComputation.executeResultWithFormalInputs,
    planned]
  simp only [Except.mapError, bind, Except.bind, preparation, executed]

/-- A post-preparation execution failure retains the exact eager input findings beside the unchanged FULL Date fault. -/
theorem checkedFullDateFirstFilled_executeResultWithFormalInputs_failure_exact
    (operation : CheckedFullDateFirstFilledComputation model)
    (input : CheckedDocument model)
    (plan : CheckedComputationFormalInputPlan model)
    (prepared : ComputationFormalInputPreparation model)
    (fault : FullDateFirstFilledComputationFault)
    (planned : operation.formalInputPlan = .ok plan)
    (preparation : plan.prepare input = .ok prepared)
    (executed : operation.executeResultWithRead input
      prepared.preliminary.readComputation
      prepared.formalErrorsInOperands = .error fault) :
    operation.executeResultWithFormalInputs input =
      .error (.execution prepared.formalErrorsInOperands fault) := by
  rw [CheckedFullDateFirstFilledComputation.executeResultWithFormalInputs,
    planned]
  simp only [Except.mapError, bind, Except.bind, preparation, executed]

/-- Application is exactly the common FullDate fold over the separately supplied document's exact cell-state projection. -/
theorem fullDateFirstFilledRun_applyToChecked_delegates
    (view : FullDateFirstFilledComputationRunView model ResidualMessage)
    (destination : CheckedDocument model) :
    view.applyToChecked destination =
      view.fullDate.applyTo destination.sourceFullDateTargetStateAt := by
  rfl

end A12Kernel
