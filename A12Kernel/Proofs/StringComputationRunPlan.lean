import A12Kernel.Elaboration.StringComputationRunPlan

/-! # Same-target String computation assembly laws

These laws expose only the checked assembly boundary. First-selected evaluation, including selected-empty termination and false-guard fall-through, remains owned by `A12Kernel.Proofs.StringAlternatives`.
-/

namespace A12Kernel

private theorem resolvedStringAlternatives_transport
    {sourceTarget target : FieldId}
    (sameTarget : sourceTarget = target)
    (alternatives : List (CheckedStringComputationAlternative model sourceTarget)) :
    List.map CheckedStringComputationAlternative.toResolved
        (sameTarget ▸ alternatives) =
      List.map CheckedStringComputationAlternative.toResolved alternatives := by
  cases sameTarget
  rfl

/-- Appending a later table preserves every resolved row in authored encounter order. -/
theorem appendSameStringTarget_resolvedAlternatives
    (left right : CheckedStringComputationTable model)
    (sameTarget : right.targetField = left.targetField)
    (samePolicy : right.targetPolicy = left.targetPolicy) :
    ((left.appendSameTarget right sameTarget samePolicy).toResolved .empty).alternatives =
      (left.toResolved .empty).alternatives ++
        (right.toResolved .empty).alternatives := by
  simp [CheckedStringComputationTable.appendSameTarget,
    CheckedStringComputationTable.toResolved,
    CheckedStringComputationTable.selectableAlternatives,
    List.map_append, resolvedStringAlternatives_transport]

/-- A same-target pair becomes one table at the first target position, using the append operation whose row-order law is stated above. -/
theorem flattenStringComputationTables_sameTarget_pair
    (left right : CheckedStringComputationTable model)
    (sameTarget : right.targetField = left.targetField)
    (samePolicy : right.targetPolicy = left.targetPolicy) :
    flattenStringComputationTables [left, right] =
      [left.appendSameTarget right sameTarget samePolicy] := by
  simp [flattenStringComputationTables, flattenStringComputationTablesFrom,
    insertStringComputationTable, sameTarget]

end A12Kernel
