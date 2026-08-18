import A12Kernel.Elaboration.DateRangeConstructionComparison
import A12Kernel.Proofs.ScalarEquality

/-! # Resolved and checked DateRange construction-equality laws -/

namespace A12Kernel

namespace EqualityOp

/-- Exchanging two classified exact DateRange values preserves equality or inequality verdict and polarity. -/
theorem evalDateRangeValues_comm (op : EqualityOp)
    (left right : SimpleComparisonOperand DateRangeValue) :
    op.evalDateRangeValues left right =
      op.evalDateRangeValues right left := by
  exact op.evalSymmetric_swapped DateRangeValue.sameEndpointInstants
    (fun _ _ => by simp [DateRangeValue.sameEndpointInstants, Bool.beq_comm])
    left right

end EqualityOp

/-- A resolved construction matches a stored range exactly when both ordered endpoint pairs agree. -/
theorem dateRangeConstruction_matches_iff
    (construction : ResolvedDateRangeConstruction)
    (stored : ResolvedDateRange) :
    (construction.resolved == stored) = true ↔
      construction.resolved = stored := by
  simp

/-- Two resolved constructions match exactly when both endpoint pairs agree. -/
theorem dateRangeConstructions_match_iff
    (left right : ResolvedDateRangeConstruction) :
    (left.resolved == right.resolved) = true ↔ left = right := by
  cases left
  cases right
  simp [ResolvedDateRangeConstruction.resolved]

/- Exact resolved DateRange equality and inequality are symmetric. -/
namespace EqualityOp

/-- Exact resolved DateRange equality and inequality are symmetric. -/
theorem evalResolvedDateRanges_comm
    (op : EqualityOp) (left right : ResolvedDateRange) :
    op.evalResolvedDateRanges left right =
      op.evalResolvedDateRanges right left := by
  exact op.evalSymmetric_swapped (· == ·) (fun _ _ => Bool.beq_comm)
    (.value left true) (.value right true)

end EqualityOp

/-- Exchanging the authored stored and constructed operands preserves the complete equality or inequality verdict. -/
theorem dateRangeConstruction_eval_position_independent
    (op : EqualityOp)
    (construction : ResolvedDateRangeConstruction)
    (stored : ResolvedDateRange) :
    op.evalDateRangeConstruction .left construction stored =
      op.evalDateRangeConstruction .right construction stored := by
  exact op.evalResolvedDateRanges_comm construction.resolved stored

/-- Exchanging two authored constructions preserves the complete equality or inequality verdict. -/
theorem dateRangeConstructions_eval_comm
    (op : EqualityOp) (left right : ResolvedDateRangeConstruction) :
    op.evalDateRangeConstructions left right =
      op.evalDateRangeConstructions right left := by
  exact op.evalResolvedDateRanges_comm left.resolved right.resolved

end A12Kernel
