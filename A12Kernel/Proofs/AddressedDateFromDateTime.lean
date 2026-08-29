import A12Kernel.Elaboration.AddressedDateFromDateTime

/-! # Exact-address `DateFromDateTime` placement certificate -/

namespace A12Kernel

/-- The checked operation places its repeatable target at or below a representable declaring group. Validity is a separate conjunct because `[]` is a prefix of every path, so containment alone would hold vacuously for an unrepresentable group. -/
theorem checkedAddressedDateFromDateTime_target_placement
    (operation : CheckedAddressedDateFromDateTime model) :
    GroupPath.isValid operation.declaringGroup = true ∧
      GroupPath.isPrefixOf operation.declaringGroup
        operation.target.checked.declaration.groupPath = true ∧
      operation.target.checked.declaration.repeatableScope ≠ [] :=
  ⟨operation.declaringGroupValid, operation.targetContainedInDeclaringGroup,
    operation.targetRepeatable⟩

end A12Kernel
