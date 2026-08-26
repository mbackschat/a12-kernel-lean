import A12Kernel.Elaboration.TimeFirstFilledComputation

/-! # Direct one-star Time `FirstFilledValue` computation laws -/

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

end A12Kernel
