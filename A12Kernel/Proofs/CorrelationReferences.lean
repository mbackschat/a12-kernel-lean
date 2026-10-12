import A12Kernel.Semantics.Correlation

namespace A12Kernel

/-- A filter's marked value reads are among its value reads. Authored repetition groups use a
    separate admission projection because naming a group does not read its descendants. -/
theorem correlatedHaving_referencesMarkedField_referencesField
    (condition : CorrelatedHaving) (field : FieldId)
    (marked : condition.referencesMarkedField field = true) :
    condition.referencesField field = true := by
  simp only [CorrelatedHaving.referencesMarkedField, CorrelatedHaving.referencesField,
    List.contains_iff_mem] at marked ⊢
  induction condition with
  | leaf leaf =>
    cases leaf with
    | numeric comparison =>
      simp only [CorrelatedHaving.markedFieldIds, CorrelatedHaving.fieldIds,
        List.mem_eraseDups, List.mem_map, List.mem_filter] at marked ⊢
      obtain ⟨atom, ⟨member, _⟩, projected⟩ := marked
      exact ⟨atom, member, projected⟩
    | simpleComparison left right comparison =>
      cases comparison <;> cases left <;> cases right <;>
        simp_all [CorrelatedHaving.markedFieldIds, CorrelatedHaving.fieldIds,
          FlatComparison.inputFields, FlatComparison.fields, List.mem_map]
    | compareStringLiteral op reference expected =>
      simp only [CorrelatedHaving.markedFieldIds, CorrelatedHaving.fieldIds] at marked ⊢
      split at marked <;> simp_all
    | stringExpression comparison | selectedComparison comparison | temporalExpression comparison | dateValidity operation source =>
      simp only [CorrelatedHaving.markedFieldIds, CorrelatedHaving.fieldIds,
        List.mem_eraseDups, List.mem_map, List.mem_filter] at marked ⊢
      obtain ⟨ref, ⟨member, _⟩, projected⟩ := marked
      exact ⟨ref, member, projected⟩
    | dateRange source | uniqueness source =>
      simp only [CorrelatedHaving.markedFieldIds, CorrelatedHaving.fieldIds,
        List.mem_eraseDups, List.mem_map, List.mem_filter] at marked ⊢
      obtain ⟨ref, ⟨member, _⟩, projected⟩ := marked
      exact ⟨ref, member, projected⟩
    | fieldMembership operator source =>
      simp only [CorrelatedHaving.markedFieldIds, CorrelatedHaving.fieldIds,
        List.mem_eraseDups, List.mem_map, List.mem_filter] at marked ⊢
      obtain ⟨ref, ⟨member, _⟩, projected⟩ := marked
      exact ⟨ref, member, projected⟩
    | literalMembership origin operator source =>
      simp only [CorrelatedHaving.markedFieldIds, CorrelatedHaving.fieldIds] at marked ⊢
      split at marked <;> simp_all
    | fieldFill operator references =>
      simp only [CorrelatedHaving.markedFieldIds, CorrelatedHaving.fieldIds,
        List.mem_eraseDups, List.mem_map, List.mem_filter] at marked ⊢
      obtain ⟨ref, ⟨member, _⟩, projected⟩ := marked
      exact ⟨ref, member, projected⟩
    | presence polarity reference =>
      simp only [CorrelatedHaving.markedFieldIds, CorrelatedHaving.fieldIds] at marked ⊢
      split at marked <;> simp_all
    | stringPattern operation reference compiled =>
      simp only [CorrelatedHaving.markedFieldIds, CorrelatedHaving.fieldIds] at marked ⊢
      split at marked <;> simp_all
    | typeValidity operation reference name =>
      simp only [CorrelatedHaving.markedFieldIds, CorrelatedHaving.fieldIds] at marked ⊢
      split at marked <;> simp_all
    | groupPresence operator origin source =>
      cases origin <;> simp_all [CorrelatedHaving.markedFieldIds, CorrelatedHaving.fieldIds]
    | groupFill operator first rest =>
      simp only [CorrelatedHaving.markedFieldIds, CorrelatedHaving.fieldIds,
        List.mem_eraseDups, List.mem_flatMap, List.mem_filter] at marked ⊢
      obtain ⟨operand, ⟨member, _⟩, projected⟩ := marked
      exact ⟨operand, member, projected⟩
  | and left right ihLeft ihRight | or left right ihLeft ihRight =>
    simp only [CorrelatedHaving.markedFieldIds, CorrelatedHaving.fieldIds,
      List.mem_eraseDups, List.mem_append] at marked ⊢
    rcases marked with inLeft | inRight
    · exact Or.inl (ihLeft inLeft)
    · exact Or.inr (ihRight inRight)

end A12Kernel
