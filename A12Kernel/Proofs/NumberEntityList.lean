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

/-- Every checked Number entity list has either a starred first slot or at least one trailing slot. -/
theorem checkedNumberEntitySource_requiredMultiplicity
    (checked : CheckedNumberEntitySource model) :
    (checked.first.isStar || !checked.rest.isEmpty) = true :=
  checked.requiredMultiplicity

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
