import A12Kernel.Elaboration.CustomFirstFilledComputation
import A12Kernel.Proofs.ExactTokenComputationResult
import A12Kernel.Proofs.StringComputationRunApplication

/-! # Custom `FirstFilledValue` laws at a fixed or a repeatable target -/

namespace A12Kernel

/-- A clean prepared Custom String remains the exact token consumed by the shared first-filled scan. -/
theorem customFirstFilledCellAt_value (value : String) :
    customFirstFilledCellAt {
      rawPresent := true, parsed := some (.str value), findings := []
    } = .present value := by
  rfl

/-- A registered Custom rejection retains its exact cause at the computation adapter. -/
theorem customFirstFilledCellAt_registeredRejection
    (value : String) (rejection : RegisteredCustomRejection) :
    customFirstFilledCellAt {
      rawPresent := true
      parsed := some (.str value)
      findings := [.registeredCustomValidation rejection]
    } = .unknown (.registeredCustomValidation rejection) := by
  rfl

/-- The checked operation retains one Custom declaration on the target and every source declaration and excludes forbidden target references; positive conditional group membership remains in the complete inventory (spec/09 §5). -/
theorem checkedCustomFirstFilled_carriers (operation : CheckedCustomFirstFilledComputation model) :
    operation.target.customType = some operation.customType ∧
      operation.site.source.declarations.all (·.customType == some operation.customType) = true ∧
      operation.referencesWith operation.targetField (·.forbidsTarget operation.targetField) = false :=
  ⟨operation.targetCustom, operation.sourceCustom, operation.excludesTarget⟩

/-- The immutable addressed executor is definitionally the caller-read route specialized to the document's checked read. -/
theorem checkedCustomFirstFilled_executeWithRead_base
    (operation : CheckedCustomFirstFilledComputation model)
    (input : CheckedDocument model) :
    operation.executeWithRead input input.read = operation.execute input := by
  rfl

/-- Result construction retains the checked operation and classifies every outcome against its exact immutable target state. -/
theorem checkedCustomFirstFilled_executeResult_projects
    (operation : CheckedCustomFirstFilledComputation model)
    (input : CheckedDocument model) (messages : List ResidualMessage)
    (outcomes : List (SourcedStringTargetOutcome CellAddr))
    (view : CustomFirstFilledComputationRunView model ResidualMessage)
    (executed : operation.execute input = .ok outcomes)
    (produced : operation.executeResult input messages = .ok view) :
    view.operation = operation ∧
      view.string = StringComputationRunView.fromSourcedOutcomes messages outcomes := by
  rw [CheckedCustomFirstFilledComputation.executeResult,
    CheckedCustomFirstFilledComputation.executeResultWithRead]
    at produced
  change operation.executeWithRead input input.read = .ok outcomes at executed
  rw [executed] at produced
  simp only [bind, Except.bind, pure, Except.pure, Except.ok.injEq] at produced
  subst view
  exact ⟨rfl, rfl⟩

/-- Checked application delegates to the established source-classified String fold. -/
theorem customFirstFilledRun_applyToChecked_delegates
    (view : CustomFirstFilledComputationRunView model ResidualMessage)
    (destination : CheckedDocument model) :
    view.applyToChecked destination =
      view.string.applyTo destination.sourceStringTargetStateAt := by
  rfl

end A12Kernel
