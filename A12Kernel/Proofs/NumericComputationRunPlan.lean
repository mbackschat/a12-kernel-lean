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

end A12Kernel
