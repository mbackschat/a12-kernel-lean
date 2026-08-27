import A12Kernel.Elaboration.AddressedDateTimeDayShiftComputation
import A12Kernel.Proofs.ComputationFormalInput

/-! # Exact-address repeatable DateTime calendar-day shift laws -/

namespace A12Kernel

/-- The repeatable calendar-day certificate excludes its target from the source and the authored amount. -/
theorem checkedAddressedDateTimeDayShiftComputation_excludes_target
    (operation : CheckedAddressedDateTimeDayShiftComputation model) :
    operation.referencesField operation.checkedTarget.targetField = false :=
  operation.targetNotReferenced

/-- The complete DateTime source remains bound by the exact repeatable target scope. -/
theorem checkedAddressedDateTimeDayShiftComputation_source_bounded
    (operation : CheckedAddressedDateTimeDayShiftComputation model) :
    operation.source.sourceDeclaration.repetitionBoundBy
        operation.checkedTarget.declaration.repeatableScope = true :=
  operation.source.sourceScopeBound

/-- Analysis retains the complete DateTime source before every authored amount dependency. -/
@[simp] theorem addressedDateTimeDayShiftComputation_fieldDependencies
    (operation : CheckedAddressedDateTimeDayShiftComputation model) :
    operation.fieldDependencies =
      operation.source.source.id :: operation.amount.fieldDependencies := by
  rfl

/-- Every addressed landing uses the concrete profile certified by the model zone. -/
theorem checkedAddressedDateTimeDayShiftComputation_profile_owned
    (operation : CheckedAddressedDateTimeDayShiftComputation model) :
    ModelZone.ConcreteProfile.ofId? model.timeZoneId = some operation.profile :=
  operation.profileMatches

/-- Result construction retains the checked operation and every exact target address. -/
theorem addressedDateTimeDayShiftComputation_executeResult_projects
    (operation : CheckedAddressedDateTimeDayShiftComputation model)
    (input : CheckedDocument model) (messages : List ResidualMessage)
    (outcomes : List AddressedDateTimeDayShiftComputationOutcome)
    (view : AddressedDateTimeDayShiftComputationRunView model ResidualMessage)
    (executed : operation.execute input = .ok outcomes)
    (produced : operation.executeResult input messages = .ok view) :
    view.operation = operation ∧
      view.dateTime = DateTimeComputationRunView.fromOutcomesAt
        input.sourceDateTimeTargetStateAt messages
        (outcomes.map fun entry => (entry.targetField, entry.outcome)) := by
  rw [CheckedAddressedDateTimeDayShiftComputation.executeResult,
    executed] at produced
  simp only [bind, Except.bind, pure, Except.pure, Except.ok.injEq] at produced
  subst view
  exact ⟨rfl, rfl⟩

/-- The composed result's formal-input channel is exactly the eager checked-plan inventory. -/
theorem addressedDateTimeDayShiftComputation_executeResultWithFormalInputs_exact
    (operation : CheckedAddressedDateTimeDayShiftComputation model)
    (input : CheckedDocument model)
    (plan : CheckedComputationFormalInputPlan model)
    (outcomes : List AddressedDateTimeDayShiftComputationOutcome)
    (view : AddressedDateTimeDayShiftComputationRunView model
      ComputationFormalInputFinding)
    (planned : operation.formalInputPlan = .ok plan)
    (executed : operation.execute input = .ok outcomes)
    (produced : operation.executeResultWithFormalInputs input = .ok view) :
    view.dateTime.formalErrorsInOperands = plan.findings input := by
  rw [CheckedAddressedDateTimeDayShiftComputation.executeResultWithFormalInputs,
    planned] at produced
  simp only [bind, Except.bind, Except.mapError] at produced
  rw [CheckedAddressedDateTimeDayShiftComputation.executeResult,
    executed] at produced
  simp only [bind, Except.bind, pure, Except.pure,
    Except.ok.injEq] at produced
  subst view
  rfl

/-- Exact-address application delegates to the common DateTime action fold. -/
theorem addressedDateTimeDayShiftComputation_applyToChecked_delegates
    (view : AddressedDateTimeDayShiftComputationRunView model ResidualMessage)
    (destination : CheckedDocument model) :
    view.applyToChecked destination =
      view.dateTime.applyTo destination.sourceDateTimeTargetStateAt := by
  rfl

end A12Kernel
