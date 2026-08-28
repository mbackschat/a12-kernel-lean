import A12Kernel.Elaboration.AddressedTimeFromDateTime
import A12Kernel.Proofs.TimeComputation

/-! # Exact-address `TimeFromDateTime` laws -/

namespace A12Kernel

/-- The immutable addressed executor is definitionally the caller-read route specialized to the document's checked read. -/
theorem checkedAddressedTimeFromDateTime_executeWithRead_base
    (operation : CheckedAddressedTimeFromDateTime model)
    (input : CheckedDocument model) :
    operation.executeWithRead input input.read = operation.execute input := by
  rfl

/-- The shared source binding ties resolution, declaration ownership, bound scope, and complete-DateTime admission to the operation's exact declaring group and target reading scope. -/
theorem checkedAddressedTimeFromDateTime_source_valid
    (operation : CheckedAddressedTimeFromDateTime model) :
    model.resolveFieldDeclarationUnchecked operation.declaringGroup
        operation.sourceBinding.sourceReference =
      .ok operation.sourceBinding.sourceDeclaration ∧
    operation.sourceBinding.sourceDeclaration.toTemporalField? =
      some operation.sourceBinding.source ∧
    operation.sourceBinding.sourceDeclaration.repetitionBoundBy
        operation.target.checked.declaration.repeatableScope = true ∧
    model.admitsCompleteDateTimeSourceIn
        operation.target.checked.declaration.repeatableScope
        operation.sourceBinding.source = true :=
  ⟨operation.sourceBinding.sourceResolved,
    operation.sourceBinding.sourceOwned,
    operation.sourceBinding.sourceScopeBound,
    operation.sourceBinding.sourceAdmitted⟩

/-- Addressed result construction retains the checked operation and classifies every executed outcome under its exact target address. -/
theorem checkedAddressedTimeFromDateTime_executeResult_projects
    (operation : CheckedAddressedTimeFromDateTime model)
    (input : CheckedDocument model) (messages : List ResidualMessage)
    (outcomes : List AddressedTimeFromDateTimeOutcome)
    (view : AddressedTimeFromDateTimeRunView model ResidualMessage)
    (executed : operation.execute input = .ok outcomes)
    (produced : operation.executeResult input messages = .ok view) :
    view.operation = operation ∧
      view.time = TimeComputationRunView.fromOutcomesAt
        input.sourceTimeTargetStateAt messages
        (outcomes.map fun entry => (entry.targetField, entry.outcome)) := by
  rw [CheckedAddressedTimeFromDateTime.executeResult,
    CheckedAddressedTimeFromDateTime.executeResultWithRead] at produced
  change operation.executeWithRead input input.read = .ok outcomes at executed
  rw [executed] at produced
  simp only [bind, Except.bind, pure, Except.pure, Except.ok.injEq] at produced
  subst view
  exact ⟨rfl, rfl⟩

/-- Addressed application is exactly the common Time fold over the separately supplied document's exact cell-state projection. -/
theorem addressedTimeFromDateTimeRun_applyToChecked_delegates
    (view : AddressedTimeFromDateTimeRunView model ResidualMessage)
    (destination : CheckedDocument model) :
    view.applyToChecked destination =
      view.time.applyTo destination.sourceTimeTargetStateAt := by
  rfl

end A12Kernel
