import A12Kernel.Proofs.AddressedNumericLeaf
import A12Kernel.Elaboration.AddressedRangeAsNumber

/-! # Same-scope repeatable `RangeAsNumber` certificate -/

namespace A12Kernel

/-- Every checked addressed range retains an evaluated String source, exact valid interval, and scale-0 Number target on one sound shared placement. -/
theorem checkedAddressedRangeAsNumber_sound
    (operation : CheckedAddressedRangeAsNumber model) :
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
      operation.placement.sourceDeclaration.toStringValueField? =
        some operation.source ∧
      validStringRange operation.start operation.finish = true ∧
      operation.placement.targetPolicy.info.scale = 0 := by
  exact ⟨checkedAddressedNumericPlacement_sound operation.placement,
    operation.sourceCertified, operation.rangeValid, operation.sameScale⟩

end A12Kernel
