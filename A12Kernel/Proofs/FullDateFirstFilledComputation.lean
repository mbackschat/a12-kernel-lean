import A12Kernel.Elaboration.FullDateFirstFilledComputation

/-! # Direct one-star full-Date `FirstFilledValue` computation laws -/

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

end A12Kernel
