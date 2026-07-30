import A12Kernel.Elaboration.AddressedNumericLeaf

/-! # Same-scope repeatable numeric-leaf placement certificate -/

namespace A12Kernel

/-- Every checked shared placement retains one validated Number target, one resolved source declaration, and their common nonempty repeatable scope. -/
theorem checkedAddressedNumericPlacement_sound
    (placement : CheckedAddressedNumericPlacement model) :
    model.validate.isOk = true ∧
      model.lookupUniqueId placement.targetField =
        .ok placement.targetDeclaration ∧
      model.resolveFieldDeclarationUnchecked
          placement.declaringGroup placement.sourceReference =
        .ok placement.sourceDeclaration ∧
      placement.targetDeclaration.groupPath =
        placement.declaringGroup ∧
      placement.targetDeclaration.toNumericTargetPolicy? =
        some placement.targetPolicy ∧
      placement.targetDeclaration.repeatableScope ≠ [] ∧
      placement.sourceDeclaration.repeatableScope =
        placement.targetDeclaration.repeatableScope := by
  exact ⟨placement.modelWellFormed, placement.targetOwned,
    placement.sourceResolved, placement.targetInDeclaringGroup,
    placement.targetPolicyOwned, placement.targetRepeatable,
    placement.sameScope⟩

end A12Kernel
