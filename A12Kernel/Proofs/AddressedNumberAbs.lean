import A12Kernel.Proofs.AddressedNumberField
import A12Kernel.Elaboration.AddressedNumberAbs

/-! # Same-scope repeatable Number `Abs` certificate -/

namespace A12Kernel

/-- Every checked addressed `Abs` retains the direct Number source's sound placement, Number-kind witness, and exact source/target scale. -/
theorem checkedAddressedNumberAbs_sound
    (operation : CheckedAddressedNumberAbs model) :
    (model.validate.isOk = true ∧
      model.lookupUniqueId operation.numberSource.placement.targetField =
        .ok operation.numberSource.placement.targetDeclaration ∧
      model.resolveFieldDeclarationUnchecked
          operation.numberSource.placement.declaringGroup
          operation.numberSource.placement.sourceReference =
        .ok operation.numberSource.placement.sourceDeclaration ∧
      operation.numberSource.placement.targetDeclaration.groupPath =
        operation.numberSource.placement.declaringGroup ∧
      operation.numberSource.placement.targetDeclaration.toNumericTargetPolicy? =
        some operation.numberSource.placement.targetPolicy ∧
      operation.numberSource.placement.targetDeclaration.repeatableScope ≠ [] ∧
      operation.numberSource.placement.sourceDeclaration.id ≠
        operation.numberSource.placement.targetField ∧
      operation.numberSource.placement.sourceDeclaration.repeatableScope =
        operation.numberSource.placement.targetDeclaration.repeatableScope) ∧
      operation.numberSource.placement.sourceDeclaration.toNumberField? =
        some operation.numberSource.source ∧
      operation.numberSource.placement.targetPolicy.info.scale =
        operation.numberSource.source.info.scale := by
  exact checkedAddressedNumberField_sound operation.numberSource

end A12Kernel
