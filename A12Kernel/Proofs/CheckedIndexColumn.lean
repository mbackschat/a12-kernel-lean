import A12Kernel.Elaboration.CheckedIndexColumn

/-! # Checked index-column laws -/

namespace A12Kernel

theorem checkedIndexColumn_wellFormed
    (column : ResolvedCheckedIndexColumn model) :
    column.WellFormed :=
  ⟨column.modelWellFormed, column.groupOwned, column.indexDeclared⟩

theorem checkedParallelIndexGroups_wellFormed
    (groups : CheckedParallelIndexGroups model) :
    groups.WellFormed :=
  ⟨groups.modelWellFormed, groups.leftGroupOwned,
    groups.rightGroupOwned, groups.leftIndexDeclared,
    groups.rightIndexDeclared, groups.groupsDistinct,
    groups.commonParent, groups.commonIndexName,
    groups.commonIndexKind, groups.exactTextIndex⟩

@[simp] theorem checkedIndexColumn_duplicate_notSemantic
    (column : ResolvedCheckedIndexColumn model) (key : SemanticIndexKey)
    (duplicate : column.duplicateKeys.contains key = true) :
    column.admitsSemanticKey key = false := by
  simp [ResolvedCheckedIndexColumn.admitsSemanticKey, duplicate]

@[simp] theorem parallelIndexSide_cleanMissing
    (group : RepeatableGroupDecl) :
    ({ group, environment := none, unavailableKey := none } :
      ResolvedParallelIndexSide).missingObservation = .empty := by
  rfl

@[simp] theorem parallelIndexSide_invalidMissing
    (group : RepeatableGroupDecl) (cause : FormalCause) :
    ({ group, environment := none, unavailableKey := some cause } :
      ResolvedParallelIndexSide).missingObservation = .unknown cause := by
  rfl

end A12Kernel
