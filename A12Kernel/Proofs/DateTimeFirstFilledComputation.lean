import A12Kernel.Elaboration.DateTimeFirstFilledComputation

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

end A12Kernel
