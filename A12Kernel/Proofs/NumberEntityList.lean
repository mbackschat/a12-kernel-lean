import A12Kernel.Elaboration.NumberEntityList
import A12Kernel.Proofs.CheckedStarDocument

/-! # Shared checked Number entity-list laws -/

namespace A12Kernel

/-- The shared checked Number query changes only the requested phase observation; address identity and structural failure remain owned by `CheckedDocument.addressedCell`. -/
theorem checkedDocument_numberValueListCellAt_delegates
    (document : CheckedDocument model) (phase : Phase)
    (environment : Env) (field : FlatNumberField)
    (addressed : CheckedAddressedCell)
    (resolved : document.addressedCell environment field.id = .ok addressed) :
    document.numberValueListCellAt phase environment field =
      .ok ((observeCell phase addressed.cell).asNumberValueListCell) := by
  unfold CheckedDocument.numberValueListCellAt
  rw [resolved]
  rfl

/-- Every checked Number entity list has either an already-many first slot or at least one trailing slot. A group slot is already-many by itself, so this is deliberately weaker than requiring a star. -/
theorem checkedNumberEntitySource_requiredMultiplicity
    (checked : CheckedNumberEntitySource model) :
    (checked.first.isAlreadyMany || !checked.rest.isEmpty) = true :=
  checked.requiredMultiplicity

/-- A retained group slot omits no descendant: every declaration anywhere in the group's recursive
    subtree is present in the slot's certified expansion. This is what lets a consumer read the
    slot's `fields` instead of re-walking the model, and it is the same extent the message reference
    channel publishes, because both go through `FlatModel.groupSubtreeFields`.

    The nearest false generalization is that the expansion is the group's **direct** children; a
    retained case refutes it on a field declared two levels down. -/
theorem checkedNumberEntityGroup_expansion_complete
    (group : CheckedNumberEntityGroup model) (declaration : FlatFieldDecl)
    (member : declaration ∈ model.groupSubtreeFields group.groupPath) :
    ∃ field, declaration.toNumberField? = some field ∧ field ∈ group.fields := by
  have admitted : declaration.toNumberField?.isSome = true :=
    List.all_eq_true.mp group.expansionAllNumber declaration member
  match hField : declaration.toNumberField? with
  | none => rw [hField] at admitted; simp at admitted
  | some field =>
      refine ⟨field, rfl, ?_⟩
      have selected : field ∈ (model.groupSubtreeFields group.source.groupPath).filterMap
          FlatFieldDecl.toNumberField? :=
        List.mem_filterMap.mpr ⟨declaration, member, hField⟩
      rw [group.expansionOwned] at selected
      simpa [CheckedNumberEntityGroup.fields] using selected

/-- Every checked Number entity list excludes repeated direct non-wildcard fields. -/
theorem checkedNumberEntitySource_uniqueDirectOperands
    (checked : CheckedNumberEntitySource model) :
    firstDuplicateDirectNumberEntityField? checked.operands = none :=
  checked.uniqueDirectOperands

/-- A wildcarded slot contributes no direct-field identity, so duplicate checking continues with the remaining slots unchanged. -/
theorem checkedNumberEntity_star_skipsDirectDuplicateGate
    (source : CheckedStarNumberSource model)
    (remaining : List (CheckedNumberEntityOperand model)) :
    firstDuplicateDirectNumberEntityField? (.star source :: remaining) =
      firstDuplicateDirectNumberEntityField? remaining := by
  rfl

/-- A filtered wildcarded slot has the same absence from the direct-field duplicate gate; its filter remains part of the runtime slot. -/
theorem checkedNumberEntity_starHaving_skipsDirectDuplicateGate
    (source : CheckedStarNumberHavingSource model)
    (remaining : List (CheckedNumberEntityOperand model)) :
    firstDuplicateDirectNumberEntityField? (.starHaving source :: remaining) =
      firstDuplicateDirectNumberEntityField? remaining := by
  rfl

/-- Filter presence is an existential property of the complete authored list, not only its first slot. -/
theorem checkedNumberEntitySource_hasHaving_of_mem
    (checked : CheckedNumberEntitySource model)
    (operand : CheckedNumberEntityOperand model)
    (member : operand ∈ checked.operands)
    (hasHaving : operand.hasHaving = true) :
    checked.hasHaving = true := by
  simp [CheckedNumberEntitySource.hasHaving, List.any_eq_true]
  exact ⟨operand, member, hasHaving⟩

/-- The semantic projection reads each already-addressed checked cell exactly once and preserves encounter order. -/
theorem resolvedCheckedNumberEntityOperand_valueListSideAt_cells
    (resolved : ResolvedCheckedNumberEntityOperand model)
    (phase : Phase) :
    (resolved.valueListSideAt phase).cells =
      resolved.addressedCells.map fun addressed =>
        (observeCell phase addressed.cell).asNumberValueListCell := by
  rfl

/-- Hierarchical tail, filter, and positional nonrelevance metadata cross the rich addressed boundary unchanged. -/
theorem resolvedCheckedNumberEntityOperand_valueListSideAt_metadata
    (resolved : ResolvedCheckedNumberEntityOperand model)
    (phase : Phase) :
    (resolved.valueListSideAt phase).hasUninstantiatedTail =
        resolved.hasUninstantiatedTail ∧
      (resolved.valueListSideAt phase).hasHaving =
        resolved.hasHaving ∧
      (resolved.valueListSideAt phase).hasNonRelevant =
  resolved.hasNonRelevant := by
  simp [ResolvedCheckedNumberEntityOperand.valueListSideAt,
    ResolvedCheckedNumberEntityOperand.hasUninstantiatedTail,
    ResolvedCheckedNumberEntityOperand.hasHaving,
    ResolvedCheckedNumberEntityOperand.hasNonRelevant]

/-- A failed starred topology remains an addressed construction error before any semantic side exists. -/
theorem checkedNumberEntityStarValidationOperand_addressing_error
    (source : CheckedStarNumberSource model)
    (document : CheckedDocument model) (outer : Env)
    (cause : StarAddressingError)
    (failed :
      source.source.path.resolve document.source.toDocument outer =
        .error cause) :
    (CheckedNumberEntityOperand.star source).resolveCheckedValidationOperand
        document outer =
      .error (.addressing cause) := by
  simp only [CheckedNumberEntityOperand.resolveCheckedValidationOperand]
  rw [resolveCheckedValidationEntityOperandCore_addressing_error
    source.source document outer none cause failed]
  rfl

end A12Kernel
