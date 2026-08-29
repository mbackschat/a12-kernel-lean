import A12Kernel.Proofs.AddressedNumericLeaf
import A12Kernel.Elaboration.AddressedFieldValueAsNumber

/-! # Repeatable `FieldValueAsNumber` certificate -/

namespace A12Kernel

/-- Every checked addressed conversion retains a certified selected textual projection and exact assignment scale on one sound shared placement. -/
theorem checkedAddressedFieldValueAsNumber_sound
    (operation : CheckedAddressedFieldValueAsNumber model) :
    (model.validate.isOk = true ∧
      model.lookupUniqueId operation.placement.targetField =
        .ok operation.placement.targetDeclaration ∧
      model.resolveFieldDeclarationUnchecked
          operation.placement.declaringGroup
          operation.placement.sourceReference =
        .ok operation.placement.sourceDeclaration ∧
      GroupPath.isPrefixOf operation.placement.declaringGroup
        operation.placement.targetDeclaration.groupPath = true ∧
      operation.placement.targetDeclaration.toNumericTargetPolicy? =
        some operation.placement.targetPolicy ∧
      operation.placement.targetDeclaration.repeatableScope ≠ [] ∧
      operation.placement.sourceDeclaration.id ≠
        operation.placement.targetField ∧
      operation.placement.sourceDeclaration.repetitionBoundBy

        operation.placement.targetDeclaration.repeatableScope = true) ∧
      operation.placement.sourceDeclaration.resolveFieldValueAsNumberSource
          operation.projectionRef = .ok operation.source ∧
      operation.source.scale =
        operation.placement.targetPolicy.info.scale := by
  exact ⟨checkedAddressedNumericPlacement_sound operation.placement,
    operation.sourceCertified, operation.sameScale⟩

end A12Kernel
