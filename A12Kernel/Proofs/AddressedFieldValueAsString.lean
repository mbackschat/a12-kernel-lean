import A12Kernel.Elaboration.AddressedFieldValueAsString

/-! # Repeatable `FieldValueAsString` certificate -/

namespace A12Kernel

/-- Every checked addressed operation retains the exact validated target, resolved Number source, ordinary String target policy, and shared nonempty repeatable scope used by execution. -/
theorem checkedAddressedFieldValueAsString_sound
    (operation : CheckedAddressedFieldValueAsString model) :
    model.validate.isOk = true ∧
      model.lookupUniqueId operation.targetField =
        .ok operation.targetDeclaration ∧
      model.resolveFieldDeclarationUnchecked
          operation.declaringGroup operation.sourceReference =
        .ok operation.sourceDeclaration ∧
      GroupPath.isValid operation.declaringGroup = true ∧
      GroupPath.isPrefixOf operation.declaringGroup
        operation.targetDeclaration.groupPath = true ∧
      operation.targetDeclaration.policy.kind = .string ∧
      operation.targetDeclaration.stringValueMode = .evaluated ∧
      operation.targetDeclaration.customType = none ∧
      operation.targetDeclaration.enumeration = none ∧
      operation.targetDeclaration.repeatableScope ≠ [] ∧
      (∃ info,
        operation.sourceDeclaration.policy.kind = .number info) ∧
      operation.sourceDeclaration.repetitionBoundBy

        operation.targetDeclaration.repeatableScope = true := by
  exact ⟨operation.modelWellFormed, operation.targetOwned,
    operation.sourceResolved, operation.declaringGroupValid,
    operation.targetContainedInDeclaringGroup,
    operation.targetString, operation.targetEvaluated,
    operation.targetOrdinary, operation.targetNotEnumerated,
    operation.targetRepeatable, operation.sourceNumber,
    operation.sourceScopeBound⟩

end A12Kernel
