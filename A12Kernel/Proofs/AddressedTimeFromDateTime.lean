import A12Kernel.Elaboration.AddressedTimeFromDateTime

/-! # Checked repeatable `TimeFromDateTime` placement laws -/

namespace A12Kernel

/-- The shared source binding ties resolution, declaration ownership, bound scope, and complete-DateTime admission to the operation's exact declaring group and target reading scope. -/
theorem checkedAddressedTimeFromDateTime_source_valid
    (operation : CheckedAddressedTimeFromDateTime model) :
    model.resolveFieldDeclarationUnchecked operation.declaringGroup
        operation.sourceBinding.sourceReference =
      .ok operation.sourceBinding.sourceDeclaration ∧
    operation.sourceBinding.sourceDeclaration.toTemporalField? =
      some operation.sourceBinding.source ∧
    operation.sourceBinding.sourceDeclaration.repetitionBoundBy
        operation.target.checked.declaration.repeatableScope = true ∧
    model.admitsCompleteDateTimeSourceIn
        operation.target.checked.declaration.repeatableScope
        operation.sourceBinding.source = true :=
  ⟨operation.sourceBinding.sourceResolved,
    operation.sourceBinding.sourceOwned,
    operation.sourceBinding.sourceScopeBound,
    operation.sourceBinding.sourceAdmitted⟩

end A12Kernel
