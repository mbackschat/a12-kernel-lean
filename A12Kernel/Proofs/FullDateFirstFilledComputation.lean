import A12Kernel.Elaboration.FullDateFirstFilledComputation
import A12Kernel.Elaboration.AddressedFullDateFirstFilledComputation

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
    executed] at produced
  simp only [bind, Except.bind, pure, Except.pure, Except.ok.injEq] at produced
  subst view
  exact ⟨rfl, rfl⟩

/-- Addressed application is exactly the common FullDate fold over the separately supplied document's exact cell-state projection. -/
theorem addressedFullDateFirstFilledRun_applyToChecked_delegates
    (view : AddressedFullDateFirstFilledComputationRunView model ResidualMessage)
    (destination : CheckedDocument model) :
    view.applyToChecked destination =
      view.fullDate.applyTo destination.sourceFullDateTargetStateAt := by
  rfl

end A12Kernel
