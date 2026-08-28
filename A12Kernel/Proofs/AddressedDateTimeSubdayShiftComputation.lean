import A12Kernel.Elaboration.AddressedDateTimeSubdayShiftComputation

/-! # Exact-address repeatable DateTime sub-day shift laws -/

namespace A12Kernel

/-- The repeatable DateTime shift certificate excludes its target from the source and every authored amount dependency. -/
theorem checkedAddressedDateTimeSubdayShiftComputation_excludes_target
    (operation : CheckedAddressedDateTimeSubdayShiftComputation model) :
    operation.referencesField operation.checkedTarget.targetField = false :=
  operation.targetNotReferenced

/-- The complete DateTime source remains bound by the exact repeatable scope used to enumerate target rows. -/
theorem checkedAddressedDateTimeSubdayShiftComputation_source_bounded
    (operation : CheckedAddressedDateTimeSubdayShiftComputation model) :
    operation.shift.source.sourceDeclaration.repetitionBoundBy
        operation.checkedTarget.declaration.repeatableScope = true :=
  operation.shift.source.sourceScopeBound

/-- Analysis retains the complete DateTime source before every authored amount dependency, including duplicates. -/
@[simp] theorem addressedDateTimeSubdayShiftComputation_fieldDependencies
    (operation : CheckedAddressedDateTimeSubdayShiftComputation model) :
    operation.fieldDependencies =
      operation.shift.source.source.id ::
        operation.shift.amount.fieldDependencies := by
  rfl

/-- Addressed result construction retains the checked operation and classifies every executed outcome under its exact target address. -/
theorem addressedDateTimeSubdayShiftComputation_executeResult_projects
    (operation : CheckedAddressedDateTimeSubdayShiftComputation model)
    (input : CheckedDocument model) (messages : List ResidualMessage)
    (outcomes : List AddressedDateTimeSubdayShiftComputationOutcome)
    (view : AddressedDateTimeSubdayShiftComputationRunView model ResidualMessage)
    (executed : operation.execute input = .ok outcomes)
    (produced : operation.executeResult input messages = .ok view) :
    view.operation = operation ∧
      view.dateTime = DateTimeComputationRunView.fromOutcomesAt
        input.sourceDateTimeTargetStateAt messages
        (outcomes.map fun entry => (entry.targetField, entry.outcome)) := by
  rw [CheckedAddressedDateTimeSubdayShiftComputation.executeResult,
    executed] at produced
  simp only [bind, Except.bind, pure, Except.pure, Except.ok.injEq] at produced
  subst view
  exact ⟨rfl, rfl⟩

/-- Whole-call composition preserves the complete addressed DateTime result after binding the eager formal-input inventory. -/
theorem addressedDateTimeSubdayShiftComputation_executeResultWithFormalInputs_exact
    (operation : CheckedAddressedDateTimeSubdayShiftComputation model)
    (input : CheckedDocument model)
    (plan : CheckedComputationFormalInputPlan model)
    (view : AddressedDateTimeSubdayShiftComputationRunView model
      ComputationFormalInputFinding)
    (planned : operation.formalInputPlan = .ok plan)
    (executed : operation.executeResult input (plan.findings input) =
      .ok view) :
    operation.executeResultWithFormalInputs input = .ok view := by
  rw [CheckedAddressedDateTimeSubdayShiftComputation.executeResultWithFormalInputs,
    planned]
  simp only [Except.mapError, Bind.bind, Except.bind]
  rw [executed]

/-- Once the addressed plan succeeds, a later structural failure retains the exact eager findings beside the unchanged fault. -/
theorem addressedDateTimeSubdayShiftComputation_executeResultWithFormalInputs_failure_exact
    (operation : CheckedAddressedDateTimeSubdayShiftComputation model)
    (input : CheckedDocument model)
    (plan : CheckedComputationFormalInputPlan model)
    (fault : AddressedDateTimeSubdayShiftComputationFault)
    (planned : operation.formalInputPlan = .ok plan)
    (executed : operation.executeResult input (plan.findings input) =
      .error fault) :
    operation.executeResultWithFormalInputs input =
      .error (.execution (plan.findings input) fault) := by
  rw [CheckedAddressedDateTimeSubdayShiftComputation.executeResultWithFormalInputs,
    planned]
  simp only [Except.mapError, Bind.bind, Except.bind]
  rw [executed]

/-- Exact-address application is the common DateTime action fold over the separately supplied document. -/
theorem addressedDateTimeSubdayShiftComputation_applyToChecked_delegates
    (view : AddressedDateTimeSubdayShiftComputationRunView model ResidualMessage)
    (destination : CheckedDocument model) :
    view.applyToChecked destination =
      view.dateTime.applyTo destination.sourceDateTimeTargetStateAt := by
  rfl

end A12Kernel
