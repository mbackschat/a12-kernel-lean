import A12Kernel.Elaboration.NumericComputation.RunPlan

/-! # Checked scalar Number run-plan laws -/

namespace A12Kernel

/-- The first-failure query is absent exactly when every table supports scalar evaluation. -/
theorem firstNonScalarNumericTable_eq_none_iff
    (tables : List (CheckedNumericComputationTable model)) :
    firstNonScalarNumericTable? tables = none ↔
      tables.all (·.supportsScalarEvaluation) = true := by
  induction tables with
  | nil => simp [firstNonScalarNumericTable?]
  | cons table remaining ih =>
      cases hScalar : table.supportsScalarEvaluation with
      | false => simp [firstNonScalarNumericTable?, hScalar]
      | true => simp [firstNonScalarNumericTable?, hScalar, ih]

/-- Every table retained by a checked scalar run satisfies the scalar evaluator boundary. -/
theorem checkedNumericComputationRun_table_scalar
    (run : CheckedNumericComputationRun model)
    (table : CheckedNumericComputationTable model)
    (member : table ∈ run.tables) :
    table.supportsScalarEvaluation = true := by
  have allScalar :=
    (firstNonScalarNumericTable_eq_none_iff run.tables).mp run.scalarTables
  exact List.all_eq_true.mp allScalar table member

private theorem selectableNumericAlternatives_transport
    {sourceTarget target : FieldId}
    {sourcePolicy targetPolicy : NumericTargetPolicy}
    (sameTarget : sourceTarget = target)
    (samePolicy : sourcePolicy = targetPolicy)
    (alternatives : List (CheckedNumericComputationAlternative
      model sourceTarget sourcePolicy)) :
    List.map CheckedNumericComputationAlternative.toSelectable
        (samePolicy ▸ (sameTarget ▸ alternatives)) =
      List.map CheckedNumericComputationAlternative.toSelectable alternatives := by
  cases sameTarget
  cases samePolicy
  rfl

private theorem numericAlternativeDeclaringGroups_transport
    {sourceTarget target : FieldId}
    {sourcePolicy targetPolicy : NumericTargetPolicy}
    (sameTarget : sourceTarget = target)
    (samePolicy : sourcePolicy = targetPolicy)
    (alternatives : List (CheckedNumericComputationAlternative
      model sourceTarget sourcePolicy)) :
    List.map (·.operation.operation.declaringGroup)
        (samePolicy ▸ (sameTarget ▸ alternatives)) =
      List.map (·.operation.operation.declaringGroup) alternatives := by
  cases sameTarget
  cases samePolicy
  rfl

/-- Appending a later same-target table preserves every selectable Number row in authored encounter order. -/
theorem appendSameNumericTarget_selectableAlternatives
    (left right : CheckedNumericComputationTable model)
    (sameTarget : right.targetField = left.targetField)
    (samePolicy : right.targetPolicy = left.targetPolicy) :
    (left.appendSameTarget right sameTarget samePolicy).selectableAlternatives =
      left.selectableAlternatives ++ right.selectableAlternatives := by
  simp only [CheckedNumericComputationTable.appendSameTarget,
    CheckedNumericComputationTable.checkedAlternatives,
    CheckedNumericComputationTable.selectableAlternatives,
    List.map_cons, List.map_append]
  rw [selectableNumericAlternatives_transport sameTarget samePolicy]
  simp

/-- Same-target Number assembly preserves every row's computation declaration group in authored order
although target-owned runtime selection does not consume it. -/
theorem appendSameNumericTarget_declaringGroups
    (left right : CheckedNumericComputationTable model)
    (sameTarget : right.targetField = left.targetField)
    (samePolicy : right.targetPolicy = left.targetPolicy) :
    (left.appendSameTarget right sameTarget samePolicy).declaringGroups =
      left.declaringGroups ++ right.declaringGroups := by
  simp only [CheckedNumericComputationTable.appendSameTarget,
    CheckedNumericComputationTable.declaringGroups,
    CheckedNumericComputationTable.checkedAlternatives,
    List.map_cons, List.map_append]
  rw [numericAlternativeDeclaringGroups_transport sameTarget samePolicy]
  simp

/-- A same-target pair becomes one table at the first target position. -/
theorem flattenNumericComputationTables_sameTarget_pair
    (left right : CheckedNumericComputationTable model)
    (sameTarget : right.targetField = left.targetField)
    (samePolicy : right.targetPolicy = left.targetPolicy) :
    flattenNumericComputationTables [left, right] =
      .ok [left.appendSameTarget right sameTarget samePolicy] := by
  simp [flattenNumericComputationTables,
    flattenNumericComputationTablesFrom,
    insertNumericComputationTable, sameTarget, samePolicy]
  congr 3

/-- A later repeated target joins its first occurrence without moving an intervening distinct target ahead of that consolidated producer. -/
theorem flattenNumericComputationTables_retainsFirstTargetPosition
    (first middle later : CheckedNumericComputationTable model)
    (sameTarget : later.targetField = first.targetField)
    (samePolicy : later.targetPolicy = first.targetPolicy)
    (middleDifferent : middle.targetField ≠ first.targetField) :
    flattenNumericComputationTables [first, middle, later] =
      .ok [
        first.appendSameTarget later sameTarget samePolicy,
        middle] := by
  simp [flattenNumericComputationTables,
    flattenNumericComputationTablesFrom,
    insertNumericComputationTable, sameTarget, samePolicy,
    middleDifferent]
  congr 3

end A12Kernel
