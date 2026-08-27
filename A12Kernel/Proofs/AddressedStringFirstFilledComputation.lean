import A12Kernel.Elaboration.AddressedStringFirstFilledComputation

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

end A12Kernel
