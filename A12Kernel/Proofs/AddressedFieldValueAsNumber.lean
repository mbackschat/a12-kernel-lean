import A12Kernel.Elaboration.AddressedFieldValueAsNumber

/-! # Same-scope repeatable `FieldValueAsNumber` certificate -/

namespace A12Kernel

/-- Every checked addressed conversion retains the exact validated Number target, certified selected textual projection, shared nonempty repeatable scope, and assignment scale used by execution. -/
theorem checkedAddressedFieldValueAsNumber_sound
    (operation : CheckedAddressedFieldValueAsNumber model) :
    model.validate.isOk = true ∧
      model.lookupUniqueId operation.targetField =
        .ok operation.targetDeclaration ∧
      model.resolveFieldDeclarationUnchecked
          operation.declaringGroup operation.sourceReference.reference =
        .ok operation.sourceDeclaration ∧
      operation.targetDeclaration.groupPath =
        operation.declaringGroup ∧
      operation.targetDeclaration.toNumericTargetPolicy? =
        some operation.targetPolicy ∧
      operation.sourceDeclaration.resolveFieldValueAsNumberSource
          operation.sourceReference.projectionRef =
        .ok operation.source ∧
      operation.targetDeclaration.repeatableScope ≠ [] ∧
      operation.sourceDeclaration.repeatableScope =
        operation.targetDeclaration.repeatableScope ∧
      operation.source.scale = operation.targetPolicy.info.scale := by
  exact ⟨operation.modelWellFormed, operation.targetOwned,
    operation.sourceResolved, operation.targetInDeclaringGroup,
    operation.targetPolicyOwned, operation.sourceCertified,
    operation.targetRepeatable, operation.sameScope, operation.sameScale⟩

end A12Kernel
