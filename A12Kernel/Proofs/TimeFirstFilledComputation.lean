import A12Kernel.Elaboration.TimeFirstFilledComputation
import A12Kernel.Elaboration.AddressedTimeFirstFilledFormalInput

/-! # Direct and exact-address Time `FirstFilledValue` computation laws -/

namespace A12Kernel

/-- A clean checked Time value retains exact clock identity and discards only its transport instant. -/
theorem timeFirstFilledCellAt_value
    (addressed : CheckedAddressedCell) (instant : Instant)
    (clock : TimeOfDay)
    (observed : observeCell .computation addressed.cell =
      .value (.temporal (.time instant clock))) :
    timeFirstFilledCellAt addressed = .value clock := by
  simp [timeFirstFilledCellAt, observed]

/-- A reached formal rejection retains its exact cause at the Time selection boundary. -/
theorem timeFirstFilledCellAt_poison
    (addressed : CheckedAddressedCell) (cause : FormalCause)
    (observed : observeCell .computation addressed.cell = .poison cause) :
    timeFirstFilledCellAt addressed = .poison cause := by
  simp [timeFirstFilledCellAt, observed]

/-- Result construction retains the operation-owned target and delegates every public projection to the established Time outcome classifier. -/
theorem timeFirstFilled_executeResult_projects
    (operation : CheckedTimeFirstFilledComputation model)
    (input : CheckedDocument model)
    (residualMessages : List ResidualMessage)
    (outcome : TimeTargetOutcome)
    (evaluated : operation.execute input = .ok outcome) :
    operation.executeResult input residualMessages =
      .ok (TimeComputationRunView.fromOutcomes input residualMessages
        [(operation.targetPolicy.checked.target.id, outcome)]) := by
  rw [CheckedTimeFirstFilledComputation.executeResult, evaluated]
  rfl

/-- The immutable addressed executor is definitionally the caller-read route specialized to the document's checked read. -/
theorem addressedTimeFirstFilled_executeWithRead_base
    (operation : CheckedAddressedTimeFirstFilledComputation model)
    (input : CheckedDocument model) :
    operation.executeWithRead input input.read = operation.execute input := by
  rfl

/-- Addressed result construction retains the checked operation and classifies every executed outcome under its exact target address. -/
theorem addressedTimeFirstFilled_executeResult_projects
    (operation : CheckedAddressedTimeFirstFilledComputation model)
    (input : CheckedDocument model) (messages : List ResidualMessage)
    (outcomes : List AddressedTimeFirstFilledComputationOutcome)
    (view : AddressedTimeFirstFilledComputationRunView model ResidualMessage)
    (executed : operation.execute input = .ok outcomes)
    (produced : operation.executeResult input messages = .ok view) :
    view.operation = operation ∧
      view.time = TimeComputationRunView.fromOutcomesAt
        input.sourceTimeTargetStateAt messages
        (outcomes.map fun entry => (entry.targetField, entry.outcome)) := by
  rw [CheckedAddressedTimeFirstFilledComputation.executeResult,
    CheckedAddressedTimeFirstFilledComputation.executeResultWithRead]
    at produced
  change operation.executeWithRead input input.read = .ok outcomes at executed
  rw [executed] at produced
  simp only [bind, Except.bind, pure, Except.pure, Except.ok.injEq] at produced
  subst view
  exact ⟨rfl, rfl⟩

/-- Successful whole-call composition preserves the exact prepared Time result, including eager findings, clock rendering, and source-relative actions. -/
theorem addressedTimeFirstFilled_executeResultWithFormalInputs_exact
    (operation : CheckedAddressedTimeFirstFilledComputation model)
    (input : CheckedDocument model)
    (plan : CheckedComputationFormalInputPlan model)
    (prepared : ComputationFormalInputPreparation model)
    (result : AddressedTimeFirstFilledComputationRunView model
      ComputationFormalInputFinding)
    (planned : operation.formalInputPlan = .ok plan)
    (preparation : plan.prepare input = .ok prepared)
    (executed : operation.executeResultWithRead input
      prepared.preliminary.readComputation
      prepared.formalErrorsInOperands = .ok result) :
    operation.executeResultWithFormalInputs input = .ok result := by
  rw [CheckedAddressedTimeFirstFilledComputation.executeResultWithFormalInputs,
    planned]
  simp only [Except.mapError, bind, Except.bind, preparation, executed]

/-- A post-preparation execution failure retains the exact eager input findings beside the unchanged addressed Time fault. -/
theorem addressedTimeFirstFilled_executeResultWithFormalInputs_failure_exact
    (operation : CheckedAddressedTimeFirstFilledComputation model)
    (input : CheckedDocument model)
    (plan : CheckedComputationFormalInputPlan model)
    (prepared : ComputationFormalInputPreparation model)
    (fault : AddressedTimeFirstFilledComputationFault)
    (planned : operation.formalInputPlan = .ok plan)
    (preparation : plan.prepare input = .ok prepared)
    (executed : operation.executeResultWithRead input
      prepared.preliminary.readComputation
      prepared.formalErrorsInOperands = .error fault) :
    operation.executeResultWithFormalInputs input =
      .error (.execution prepared.formalErrorsInOperands fault) := by
  rw [CheckedAddressedTimeFirstFilledComputation.executeResultWithFormalInputs,
    planned]
  simp only [Except.mapError, bind, Except.bind, preparation, executed]

/-- Addressed application is exactly the common Time fold over the separately supplied document's exact cell-state projection. -/
theorem addressedTimeFirstFilledRun_applyToChecked_delegates
    (view : AddressedTimeFirstFilledComputationRunView model ResidualMessage)
    (destination : CheckedDocument model) :
    view.applyToChecked destination =
      view.time.applyTo destination.sourceTimeTargetStateAt := by
  rfl

end A12Kernel
