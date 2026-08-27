import A12Kernel.Elaboration.NumericComputation.FormalInput

/-! # Checked numeric-computation formal-input laws -/

namespace A12Kernel

/-- The concrete dependency inventory is exactly the validated model declarations referenced by the checked expression. -/
theorem checkedNumericComputationOperation_fieldDependencies_exact
    (operation : CheckedNumericComputationOperation model)
    (field : FieldId) :
    field ∈ operation.fieldDependencies ↔
      ∃ declaration ∈ model.fields,
        declaration.id = field ∧
          operation.core.expression.anyAtom
            (CheckedNumericComputationAtom.references model declaration.id) = true := by
  rw [CheckedNumericComputationOperation.fieldDependencies, List.mem_map]
  constructor
  · rintro ⟨declaration, member, equality⟩
    rw [List.mem_filter] at member
    exact ⟨declaration, member.1, equality, member.2⟩
  · rintro ⟨declaration, member, equality, referenced⟩
    exact ⟨declaration, by simpa using And.intro member referenced, equality⟩

/-- The table dependency inventory is exactly the validated declarations referenced by at least one checked alternative guard or operation. -/
theorem checkedNumericComputationTable_fieldDependencies_exact
    (table : CheckedNumericComputationTable model)
    (field : FieldId) :
    field ∈ table.fieldDependencies ↔
      ∃ declaration ∈ model.fields,
        declaration.id = field ∧ table.referencesField declaration.id = true := by
  rw [CheckedNumericComputationTable.fieldDependencies, List.mem_map]
  constructor
  · rintro ⟨declaration, member, equality⟩
    rw [List.mem_filter] at member
    exact ⟨declaration, member.1, equality, member.2⟩
  · rintro ⟨declaration, member, equality, referenced⟩
    exact ⟨declaration, by simpa using And.intro member referenced, equality⟩

end A12Kernel
