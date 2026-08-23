import A12Kernel.Proofs.AddressedNumericLeaf
import A12Kernel.Elaboration.AddressedStringLength

/-! # Repeatable String `Length` certificate -/

namespace A12Kernel

/-- Every checked addressed Length retains an evaluated String source and scale-0 Number target on one sound shared placement. -/
theorem checkedAddressedStringLength_sound
    (operation : CheckedAddressedStringLength model) :
    (model.validate.isOk = true ∧
      model.lookupUniqueId operation.placement.targetField =
        .ok operation.placement.targetDeclaration ∧
      model.resolveFieldDeclarationUnchecked
          operation.placement.declaringGroup
          operation.placement.sourceReference =
        .ok operation.placement.sourceDeclaration ∧
      operation.placement.targetDeclaration.groupPath =
        operation.placement.declaringGroup ∧
      operation.placement.targetDeclaration.toNumericTargetPolicy? =
        some operation.placement.targetPolicy ∧
      operation.placement.targetDeclaration.repeatableScope ≠ [] ∧
      operation.placement.sourceDeclaration.id ≠
        operation.placement.targetField ∧
      operation.placement.sourceDeclaration.repetitionBoundBy

        operation.placement.targetDeclaration.repeatableScope = true) ∧
      operation.placement.sourceDeclaration.toStringValueField? =
        some operation.source ∧
      operation.placement.targetPolicy.info.scale = 0 := by
  exact ⟨checkedAddressedNumericPlacement_sound operation.placement,
    operation.sourceCertified, operation.sameScale⟩

end A12Kernel
