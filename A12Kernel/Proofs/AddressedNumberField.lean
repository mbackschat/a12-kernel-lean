import A12Kernel.Proofs.AddressedNumericLeaf
import A12Kernel.Elaboration.AddressedNumberField

/-! # Same-scope repeatable direct Number-field certificate -/

namespace A12Kernel

/-- Every checked direct Number-field operation retains one sound placement, Number source, and exact source/target scale. -/
theorem checkedAddressedNumberField_sound
    (operation : CheckedAddressedNumberField model) :
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
      operation.placement.sourceDeclaration.repeatableScope =
        operation.placement.targetDeclaration.repeatableScope) ∧
      operation.placement.sourceDeclaration.toNumberField? =
        some operation.source ∧
      operation.placement.targetPolicy.info.scale =
        operation.source.info.scale := by
  exact ⟨checkedAddressedNumericPlacement_sound operation.placement,
    operation.sourceCertified, operation.sameScale⟩

end A12Kernel
