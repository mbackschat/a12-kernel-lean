import A12Kernel.Elaboration.AddressedNumericLeaf

/-! # Repeatable numeric-leaf placement certificate -/

namespace A12Kernel

/-- Every checked shared placement retains one validated Number target at a nonempty repeatable scope, one resolved source declaration, and the fact that the target's scope binds every repeatable level the source crosses. -/
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
      placement.sourceDeclaration.id ≠ placement.targetField ∧
      placement.sourceDeclaration.repetitionBoundBy
        placement.targetDeclaration.repeatableScope = true := by
  exact ⟨placement.modelWellFormed, placement.targetOwned,
    placement.sourceResolved, placement.targetInDeclaringGroup,
    placement.targetPolicyOwned, placement.targetRepeatable,
    placement.sourceNotTarget, placement.sourceScopeBound⟩

end A12Kernel
