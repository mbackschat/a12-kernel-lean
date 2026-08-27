import A12Kernel.Elaboration.TimeFirstFilledComputation
import A12Kernel.Elaboration.AddressedTimeFirstFilledComputation

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
    executed] at produced
  simp only [bind, Except.bind, pure, Except.pure, Except.ok.injEq] at produced
  subst view
  exact ⟨rfl, rfl⟩

/-- Addressed application is exactly the common Time fold over the separately supplied document's exact cell-state projection. -/
theorem addressedTimeFirstFilledRun_applyToChecked_delegates
    (view : AddressedTimeFirstFilledComputationRunView model ResidualMessage)
    (destination : CheckedDocument model) :
    view.applyToChecked destination =
      view.time.applyTo destination.sourceTimeTargetStateAt := by
  rfl

end A12Kernel
