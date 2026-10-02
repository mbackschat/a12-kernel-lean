import A12Kernel.Elaboration.TimeFirstFilledComputation

/-! # Time `FirstFilledValue` laws at a fixed or a repeatable target -/

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

/-- The immutable-document executor is definitionally the caller-read route specialized to the document's checked read. -/
theorem checkedTimeFirstFilled_executeWithRead_base
    (operation : CheckedTimeFirstFilledComputation model)
    (input : CheckedDocument model) :
    operation.executeWithRead input input.read = operation.execute input := by
  rfl

/-- Result construction retains the checked operation and classifies every executed outcome under its exact target address. -/
theorem checkedTimeFirstFilled_executeResult_projects
    (operation : CheckedTimeFirstFilledComputation model)
    (input : CheckedDocument model) (messages : List ResidualMessage)
    (outcomes : List TimeFirstFilledComputationOutcome)
    (view : TimeFirstFilledComputationRunView model ResidualMessage)
    (executed : operation.execute input = .ok outcomes)
    (produced : operation.executeResult input messages = .ok view) :
    view.operation = operation ∧
      view.time = TimeComputationRunView.fromOutcomesAt
        input.sourceTimeTargetStateAt messages
        (outcomes.map fun entry => (entry.targetField, entry.outcome)) := by
  rw [CheckedTimeFirstFilledComputation.executeResult,
    CheckedTimeFirstFilledComputation.executeResultWithRead]
    at produced
  change operation.executeWithRead input input.read = .ok outcomes at executed
  rw [executed] at produced
  simp only [bind, Except.bind, pure, Except.pure, Except.ok.injEq] at produced
  subst view
  exact ⟨rfl, rfl⟩

/-- Application is exactly the common Time fold over the separately supplied document's exact cell-state projection. -/
theorem timeFirstFilledRun_applyToChecked_delegates
    (view : TimeFirstFilledComputationRunView model ResidualMessage)
    (destination : CheckedDocument model) :
    view.applyToChecked destination =
      view.time.applyTo destination.sourceTimeTargetStateAt := by
  rfl

end A12Kernel
