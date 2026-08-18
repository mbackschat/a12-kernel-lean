import A12Kernel.Semantics.DateRangeComparison
import A12Kernel.Proofs.ScalarEquality

/-! # Resolved DateRange construction-equality laws -/

namespace A12Kernel

/-- A resolved construction matches a stored range exactly when both ordered endpoint pairs agree. -/
theorem dateRangeConstruction_matches_iff
    (construction : ResolvedDateRangeConstruction)
    (stored : ResolvedDateRange) :
    (construction.resolved == stored) = true ↔
      construction.resolved = stored := by
  simp

/-- Exchanging the authored stored and constructed operands preserves the complete equality or inequality verdict. -/
theorem dateRangeConstruction_eval_position_independent
    (op : EqualityOp)
    (construction : ResolvedDateRangeConstruction)
    (stored : ResolvedDateRange) :
    op.evalDateRangeConstruction .left construction stored =
      op.evalDateRangeConstruction .right construction stored := by
  exact op.evalSymmetric_swapped (· == ·) (fun _ _ => Bool.beq_comm)
    (.value construction.resolved true) (.value stored true)

end A12Kernel
