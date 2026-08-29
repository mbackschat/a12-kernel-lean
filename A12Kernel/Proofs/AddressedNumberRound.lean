import A12Kernel.Proofs.AddressedNumberField
import A12Kernel.Elaboration.AddressedNumberRound

/-! # Repeatable direct-Number rounding certificate -/

namespace A12Kernel

/-- Every checked addressed rounding operation retains one sound Number source and a target scale equal to its authored places. -/
theorem checkedAddressedNumberRound_sound
    (operation : CheckedAddressedNumberRound model) :
    (model.validate.isOk = true ∧
      model.lookupUniqueId operation.numberSource.placement.targetField =
        .ok operation.numberSource.placement.targetDeclaration ∧
      model.resolveFieldDeclarationUnchecked
          operation.numberSource.placement.declaringGroup
          operation.numberSource.placement.sourceReference =
        .ok operation.numberSource.placement.sourceDeclaration ∧
      GroupPath.isValid operation.numberSource.placement.declaringGroup = true ∧
      GroupPath.isPrefixOf operation.numberSource.placement.declaringGroup
        operation.numberSource.placement.targetDeclaration.groupPath = true ∧
      operation.numberSource.placement.targetDeclaration.toNumericTargetPolicy? =
        some operation.numberSource.placement.targetPolicy ∧
      operation.numberSource.placement.targetDeclaration.repeatableScope ≠ [] ∧
      operation.numberSource.placement.sourceDeclaration.id ≠
        operation.numberSource.placement.targetField ∧
      operation.numberSource.placement.sourceDeclaration.repetitionBoundBy

        operation.numberSource.placement.targetDeclaration.repeatableScope = true) ∧
      operation.numberSource.placement.sourceDeclaration.toNumberField? =
        some operation.numberSource.source ∧
      operation.numberSource.placement.targetPolicy.info.scale =
        operation.places.val := by
  rcases checkedAddressedNumberSource_sound operation.numberSource with
    ⟨placement, certified⟩
  exact ⟨placement, certified, operation.sameScale⟩

end A12Kernel
