import A12Kernel.Proofs.AddressedNumericLeaf
import A12Kernel.Elaboration.AddressedNumberField

/-! # Repeatable direct Number-field certificate -/

namespace A12Kernel

/-- Every shared addressed Number source retains one sound placement and exact Number-kind witness. -/
theorem checkedAddressedNumberSource_sound
    (source : CheckedAddressedNumberSource model) :
    (model.validate.isOk = true ∧
      model.lookupUniqueId source.placement.targetField =
        .ok source.placement.targetDeclaration ∧
      model.resolveFieldDeclarationUnchecked
          source.placement.declaringGroup source.placement.sourceReference =
        .ok source.placement.sourceDeclaration ∧
      source.placement.targetDeclaration.groupPath =
        source.placement.declaringGroup ∧
      source.placement.targetDeclaration.toNumericTargetPolicy? =
        some source.placement.targetPolicy ∧
      source.placement.targetDeclaration.repeatableScope ≠ [] ∧
      source.placement.sourceDeclaration.id ≠ source.placement.targetField ∧
      source.placement.sourceDeclaration.repetitionBoundBy

        source.placement.targetDeclaration.repeatableScope = true) ∧
      source.placement.sourceDeclaration.toNumberField? = some source.source := by
  exact ⟨checkedAddressedNumericPlacement_sound source.placement,
    source.sourceCertified⟩

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
      operation.placement.sourceDeclaration.repetitionBoundBy

        operation.placement.targetDeclaration.repeatableScope = true) ∧
      operation.placement.sourceDeclaration.toNumberField? =
        some operation.source ∧
      operation.placement.targetPolicy.info.scale =
        operation.source.info.scale := by
  rcases checkedAddressedNumberSource_sound
      operation.toCheckedAddressedNumberSource with ⟨placement, certified⟩
  exact ⟨placement, certified, operation.sameScale⟩

@[simp]
theorem checkedAddressedNumberPair_evaluateAtEnvironmentWithRead_left_poison (pair : CheckedAddressedNumberPair model)
    (read : CellAddr → Except CheckedDocumentError CheckedCell)
    (combine : NumericComputationResult → NumericComputationResult → NumericComputationResult)
    (environment : Env) (cause : FormalCause)
    (leftPoison : pair.left.evaluateAtEnvironmentWithRead read environment =
      .ok (.poison cause)) :
    pair.evaluateAtEnvironmentWithRead read combine environment = .ok (.poison cause) := by
  rw [CheckedAddressedNumberPair.evaluateAtEnvironmentWithRead, leftPoison]
  simp only [Bind.bind, Except.bind, Pure.pure, Except.pure]

end A12Kernel
