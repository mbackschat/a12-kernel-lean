import A12Kernel.Elaboration.AddressedStringFirstFilledComputation
import A12Kernel.Proofs.StringComputationRunApplication

/-! # Exact-address repeatable ordinary String `FirstFilledValue` laws -/

namespace A12Kernel

/-- The checked operation retains ordinary String carriers and one sibling-star axis whose nonempty binding prefix is supplied by the target scope. -/
theorem checkedAddressedStringFirstFilled_carriersAndPlacement
    (operation : CheckedAddressedStringFirstFilledComputation model) :
    operation.target.isOrdinaryStringComputationCarrier = true ∧
      operation.source.declaration.isOrdinaryStringComputationCarrier = true ∧
      operation.source.reopenedScope.length = 1 ∧
      operation.source.bindingScope ≠ [] ∧
      operation.source.bindingScope.isPrefixOf
        operation.target.repeatableScope = true ∧
      operation.source.bindingScope ≠ operation.target.repeatableScope ∧ operation.source.declaration.id ≠ operation.targetField ∧
      operation.source.bindingScope.all
        operation.target.repeatableScope.contains = true :=
  ⟨operation.targetOrdinary, operation.sourceOrdinary,
    operation.placement.sourceSingleReopenedAxis,
    operation.placement.sourceBindingNonempty,
    operation.sourceBindingPrefix, operation.sourceBindingStrict, operation.placement.targetNotReferenced,
    operation.placement.sourceBindingBound⟩

/-- Addressed result construction retains the checked operation and classifies every outcome against its exact immutable target state. -/
theorem checkedAddressedStringFirstFilled_executeResult_projects
    (operation : CheckedAddressedStringFirstFilledComputation model)
    (patterns : PreparedFlatStringPatterns model compilePattern)
    (input : CheckedDocument model) (messages : List ResidualMessage)
    (outcomes : List AddressedStringFirstFilledComputationOutcome)
    (view : AddressedStringFirstFilledComputationRunView model ResidualMessage)
    (executed : operation.execute patterns input = .ok outcomes)
    (produced : operation.executeResult patterns input messages = .ok view) :
    view.operation = operation ∧
      view.string = StringComputationRunView.fromSourcedOutcomes messages
        (outcomes.map fun entry => {
          targetField := entry.targetField
          outcome := entry.outcome
          source := input.sourceStringTargetStateAt entry.targetField
        }) := by
  rw [CheckedAddressedStringFirstFilledComputation.executeResult, executed]
    at produced
  simp only [bind, Except.bind, pure, Except.pure, Except.ok.injEq] at produced
  subst view
  exact ⟨rfl, rfl⟩

/-- Exact-address checked application delegates to the established source-classified String fold. -/
theorem addressedStringFirstFilledRun_applyToChecked_delegates
    (view : AddressedStringFirstFilledComputationRunView model ResidualMessage)
    (destination : CheckedDocument model) :
    view.applyToChecked destination =
      view.string.applyTo destination.sourceStringTargetStateAt := by
  rfl

end A12Kernel
