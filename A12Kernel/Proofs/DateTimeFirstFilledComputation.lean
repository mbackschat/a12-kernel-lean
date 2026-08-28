import A12Kernel.Elaboration.DateTimeFirstFilledComputation
import A12Kernel.Elaboration.AddressedDateTimeFirstFilledFormalInput

/-! # Direct one-star DateTime `FirstFilledValue` computation laws -/

namespace A12Kernel

/-- A clean DateTime value retains exact instant identity before target-zone rendering. -/
theorem dateTimeFirstFilledCellAt_value (addressed : CheckedAddressedCell) (instant : Instant)
    (parts : DateParts) (clock : TimeOfDay) (basis : DateCalendarBasis)
    (observed : observeCell .computation addressed.cell = .value (.temporal (.dateTime instant parts clock basis))) :
    dateTimeFirstFilledCellAt addressed = .value instant := by
  simp [dateTimeFirstFilledCellAt, observed]

/-- A reached formal rejection retains its exact cause at the DateTime selection boundary. -/
theorem dateTimeFirstFilledCellAt_poison (addressed : CheckedAddressedCell) (cause : FormalCause)
    (observed : observeCell .computation addressed.cell = .poison cause) :
    dateTimeFirstFilledCellAt addressed = .poison cause := by
  simp [dateTimeFirstFilledCellAt, observed]

/-- Result construction retains the operation-owned target and delegates every public projection to the established DateTime outcome classifier. -/
theorem dateTimeFirstFilled_executeResult_projects
    (operation : CheckedDateTimeFirstFilledComputation model)
    (input : CheckedDocument model)
    (residualMessages : List ResidualMessage)
    (outcome : DateTimeTargetOutcome)
    (evaluated : operation.execute input = .ok outcome) :
    operation.executeResult input residualMessages =
      .ok (DateTimeComputationRunView.fromOutcomes input residualMessages
        [(operation.targetPolicy.checked.target.id, outcome)]) := by
  rw [CheckedDateTimeFirstFilledComputation.executeResult, evaluated]
  rfl

/-- The immutable addressed executor is definitionally the caller-read route specialized to the document's checked read. -/
theorem addressedDateTimeFirstFilled_executeWithRead_base
    (operation : CheckedAddressedDateTimeFirstFilledComputation model)
    (input : CheckedDocument model) :
    operation.executeWithRead input input.read = operation.execute input := by
  rfl

/-- Addressed result construction retains the checked operation and classifies every executed outcome under its exact target address. -/
theorem addressedDateTimeFirstFilled_executeResult_projects
    (operation : CheckedAddressedDateTimeFirstFilledComputation model)
    (input : CheckedDocument model) (messages : List ResidualMessage)
    (outcomes : List AddressedDateTimeFirstFilledComputationOutcome)
    (view : AddressedDateTimeFirstFilledComputationRunView model ResidualMessage)
    (executed : operation.execute input = .ok outcomes)
    (produced : operation.executeResult input messages = .ok view) :
    view.operation = operation ∧
      view.dateTime = DateTimeComputationRunView.fromOutcomesAt
        input.sourceDateTimeTargetStateAt messages
        (outcomes.map fun entry => (entry.targetField, entry.outcome)) := by
  rw [CheckedAddressedDateTimeFirstFilledComputation.executeResult,
    CheckedAddressedDateTimeFirstFilledComputation.executeResultWithRead]
    at produced
  change operation.executeWithRead input input.read = .ok outcomes at executed
  rw [executed] at produced
  simp only [bind, Except.bind, pure, Except.pure, Except.ok.injEq] at produced
  subst view
  exact ⟨rfl, rfl⟩

/-- Successful whole-call composition preserves the exact prepared DateTime result, including eager findings, model-zone rendering, and source-relative actions. -/
theorem addressedDateTimeFirstFilled_executeResultWithFormalInputs_exact
    (operation : CheckedAddressedDateTimeFirstFilledComputation model)
    (input : CheckedDocument model)
    (plan : CheckedComputationFormalInputPlan model)
    (prepared : ComputationFormalInputPreparation model)
    (result : AddressedDateTimeFirstFilledComputationRunView model
      ComputationFormalInputFinding)
    (planned : operation.formalInputPlan = .ok plan)
    (preparation : plan.prepare input = .ok prepared)
    (executed : operation.executeResultWithRead input
      prepared.preliminary.readComputation
      prepared.formalErrorsInOperands = .ok result) :
    operation.executeResultWithFormalInputs input = .ok result := by
  rw [CheckedAddressedDateTimeFirstFilledComputation.executeResultWithFormalInputs,
    planned]
  simp only [Except.mapError, bind, Except.bind, preparation, executed]

/-- A post-preparation execution failure retains the exact eager input findings beside the unchanged addressed DateTime fault. -/
theorem addressedDateTimeFirstFilled_executeResultWithFormalInputs_failure_exact
    (operation : CheckedAddressedDateTimeFirstFilledComputation model)
    (input : CheckedDocument model)
    (plan : CheckedComputationFormalInputPlan model)
    (prepared : ComputationFormalInputPreparation model)
    (fault : AddressedDateTimeFirstFilledComputationFault)
    (planned : operation.formalInputPlan = .ok plan)
    (preparation : plan.prepare input = .ok prepared)
    (executed : operation.executeResultWithRead input
      prepared.preliminary.readComputation
      prepared.formalErrorsInOperands = .error fault) :
    operation.executeResultWithFormalInputs input =
      .error (.execution prepared.formalErrorsInOperands fault) := by
  rw [CheckedAddressedDateTimeFirstFilledComputation.executeResultWithFormalInputs,
    planned]
  simp only [Except.mapError, bind, Except.bind, preparation, executed]

/-- Addressed application is exactly the common DateTime fold over the separately supplied document's exact cell-state projection. -/
theorem addressedDateTimeFirstFilledRun_applyToChecked_delegates
    (view : AddressedDateTimeFirstFilledComputationRunView model ResidualMessage)
    (destination : CheckedDocument model) :
    view.applyToChecked destination =
      view.dateTime.applyTo destination.sourceDateTimeTargetStateAt := by
  rfl

end A12Kernel
