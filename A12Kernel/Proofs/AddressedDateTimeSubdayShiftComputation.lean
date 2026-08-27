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

/-- Exact-address application is the common DateTime action fold over the separately supplied document. -/
theorem addressedDateTimeSubdayShiftComputation_applyToChecked_delegates
    (view : AddressedDateTimeSubdayShiftComputationRunView model ResidualMessage)
    (destination : CheckedDocument model) :
    view.applyToChecked destination =
      view.dateTime.applyTo destination.sourceDateTimeTargetStateAt := by
  rfl

end A12Kernel
