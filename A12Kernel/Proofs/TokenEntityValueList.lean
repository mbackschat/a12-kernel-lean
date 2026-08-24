import A12Kernel.Elaboration.TokenEntityValueList

/-! # Checked mixed token entity-list value-list laws -/

namespace A12Kernel

/-- The combined checked source excludes a repeated exact direct String or Enumeration/category reference across either authored side. -/
theorem checkedTokenEntityValueList_uniqueDirectOperands
    (checked : CheckedTokenEntityValueListSource model) :
    firstDuplicateDirectTokenField?
      (checked.fields.operands ++ checked.values.operands) = none :=
  checked.uniqueDirectOperands

/-- Both checked sides retain the same statically admitted String or Enumeration base family. -/
theorem checkedTokenEntityValueList_commonFamily
    (checked : CheckedTokenEntityValueListSource model) :
    checked.fields.valueListFamily? = some checked.family ∧
      checked.values.valueListFamily? = some checked.family :=
  ⟨checked.fieldsFamily, checked.valuesFamily⟩

/-- **The retained group expansion omits no descendant.** Every declaration in the group's recursive subtree reaches the certified slot list, so a consumer reading the expansion off the slot sees the same extent the checker scanned. The `expansionAllToken` obligation is what makes this a completeness claim rather than a filter: without it a subtree of Numbers would certify as an empty selection. -/
theorem checkedTokenEntityGroup_expansion_complete
    (group : CheckedTokenEntityGroup model) (declaration : FlatFieldDecl)
    (member : declaration ∈ model.groupSubtreeFields group.groupPath) :
    ∃ slot, declaration.toStoredTokenSlot? = some slot ∧ slot ∈ group.slots := by
  have admitted : declaration.toStoredTokenSlot?.isSome = true :=
    List.all_eq_true.mp group.expansionAllToken declaration member
  match hSlot : declaration.toStoredTokenSlot? with
  | none => rw [hSlot] at admitted; simp at admitted
  | some slot =>
      refine ⟨slot, rfl, ?_⟩
      have selected : slot ∈ (model.groupSubtreeFields group.source.groupPath).filterMap
          FlatFieldDecl.toStoredTokenSlot? :=
        List.mem_filterMap.mpr ⟨declaration, member, hSlot⟩
      rw [group.expansionOwned] at selected
      simpa [CheckedTokenEntityGroup.slots] using selected

/-- A resolved Enumeration token operand carries exactly the projection that was asked for, so no slot can silently read a different category than the one it authored. -/
theorem enumerationTextFieldComparison_projectionRef
    {declaration : FlatFieldDecl} {projectionRef : EnumerationProjectionRef}
    {operand : FlatTextFieldOperand} {profile : DirectComparableField}
    (owned :
      declaration.toEnumerationTextFieldComparison? projectionRef =
        some (operand, profile)) :
    operand.projectionRef? = some projectionRef := by
  unfold FlatFieldDecl.toEnumerationTextFieldComparison? at owned
  split at owned
  · split at owned
    · split at owned
      · cases owned; rfl
      · exact absurd owned (by simp)
    · exact absurd owned (by simp)
  · exact absurd owned (by simp)

/-- A slot that authors no read form reads its declaration in the stored form. String carries no Enumeration projection at all, and the Enumeration arm resolves the stored one by the law above. -/
theorem textFieldComparison_projectionRef_stored
    {declaration : FlatFieldDecl} {operand : FlatTextFieldOperand}
    {profile : DirectComparableField}
    (owned : declaration.toTextFieldComparison? = some (operand, profile)) :
    operand.projectionRef? = none ∨
      operand.projectionRef? = some .stored := by
  unfold FlatFieldDecl.toTextFieldComparison? at owned
  split at owned
  · cases owned; exact Or.inl rfl
  · exact Or.inr (enumerationTextFieldComparison_projectionRef owned)
  · exact absurd owned (by simp)

/-- **A group slot cannot smuggle a category read.** `SurfaceFieldEntityOperand.group` carries no `FieldEntityReadForm` where `.field` does, so every declaration a group reaches is read in its stored form. That is a consequence of the authored surface rather than a claim about the Kernel, and it is what lets one group slot certify against the stored projection alone. -/
theorem checkedTokenEntityGroup_projections_stored
    (group : CheckedTokenEntityGroup model) :
    ∀ reference ∈ (CheckedTokenEntityOperand.group group).projectionRefs,
      reference = none ∨ reference = some .stored := by
  intro reference member
  simp only [CheckedTokenEntityOperand.projectionRefs,
    CheckedTokenEntityOperand.tokenOperands, List.map_map,
    List.mem_map] at member
  obtain ⟨slot, slotMember, projected⟩ := member
  have selected : slot ∈ (model.groupSubtreeFields group.source.groupPath).filterMap
      FlatFieldDecl.toStoredTokenSlot? := by
    rw [group.expansionOwned]
    simpa [CheckedTokenEntityGroup.slots] using slotMember
  obtain ⟨declaration, _, owned⟩ := List.mem_filterMap.mp selected
  simp only [FlatFieldDecl.toStoredTokenSlot?, FlatFieldDecl.toTokenFieldComparison?,
    Option.map_eq_some_iff] at owned
  obtain ⟨⟨resolved, _⟩, comparison, rebuilt⟩ := owned
  have operandOwned : slot.operand = resolved := by
    rw [← rebuilt]
  rw [← projected]
  simp only [Function.comp_apply, operandOwned]
  exact textFieldComparison_projectionRef_stored comparison

/-- Complete partial relevance for one group slot means complete value-list extent for every declaration in its certified recursive expansion, at the levels the authored group operand reopens. -/
theorem checkedTokenEntityGroup_partialExtentRelevant_iff
    (group : CheckedTokenEntityGroup model)
    (scope : ValidationRelevanceScope) (outer : Env) :
    group.partialExtentRelevant scope outer = true ↔
      ∀ slot ∈ group.slots,
        scope.coversValueListExtent model slot.declaration.path
          (slot.declaration.repeatableScope.take group.source.boundLevelCount)
          (slot.declaration.repeatableScope.drop group.source.boundLevelCount)
          outer = true := by
  simp [CheckedTokenEntityGroup.partialExtentRelevant]

/-- Each reached cell is projected through the operand paired with it in the resolving walk: a field-denoting slot's one certified operand, or, for a group, the declaration that actually stored the cell. -/
theorem resolvedCheckedTokenEntityOperand_valueListSideAt_cells
    (resolved : ResolvedCheckedTokenEntityOperand model) (phase : Phase) :
    (resolved.valueListSideAt phase).cells =
      resolved.projectedCells.map fun pair =>
        pair.1.checkedValueListCellAt phase pair.2.cell := by
  rfl

/-- Rich two-sided execution is exactly the existing ordered evaluator over the typed addressed projections. -/
theorem resolvedCheckedTokenEntityValueList_evaluate_delegates
    (resolved : ResolvedCheckedTokenEntityValueList model) :
    resolved.evaluate =
      resolved.quantifier.evalOrdered
        (resolved.fields.map (·.valueListSideAt .validation))
        (resolved.values.map (·.valueListSideAt .validation)) := by
  rfl

end A12Kernel
