import A12Kernel.Proofs.DateComparison
import A12Kernel.Semantics.DateTimeComparison

/-! # Resolved DateTime instant-comparison laws -/

namespace A12Kernel

/-- Resolved DateTime equality fires exactly on identical physical instants. -/
theorem dateTimeComparison_equal_iff (left right : Instant) :
    DateComparisonOp.equal.holdsInstant left right = true ↔ left = right := by
  simp [DateComparisonOp.holdsInstant]

/-- Resolved DateTime inequality fires exactly on distinct physical instants. -/
theorem dateTimeComparison_notEqual_iff (left right : Instant) :
    DateComparisonOp.notEqual.holdsInstant left right = true ↔ left ≠ right := by
  simp [DateComparisonOp.holdsInstant]

/-- Exchanging instants and the directional operator preserves every resolved comparison result. -/
theorem dateTimeComparison_swapped (op : DateComparisonOp)
    (left right : Instant) :
    op.swapped.holdsInstant left right = op.holdsInstant right left := by
  cases op with
  | equal => exact Bool.beq_comm
  | notEqual => exact congrArg (!·) Bool.beq_comm
  | before | beforeOrEqual | after | afterOrEqual => rfl

/-- A strict instant comparison cannot hold in both directions. -/
theorem dateTimeComparison_before_excludes_after (left right : Instant)
    (before : DateComparisonOp.before.holdsInstant left right = true) :
    DateComparisonOp.after.holdsInstant left right = false := by
  simp [DateComparisonOp.holdsInstant] at before ⊢
  omega

/-- Operand exchange plus the matching directional operator preserves classified DateTime verdicts and polarity. -/
theorem dateTimeComparison_eval_swapped (op : DateComparisonOp)
    (left right : SimpleComparisonOperand Instant) :
    op.swapped.evalInstant left right = op.evalInstant right left := by
  exact evalSymmetricComparison_swapped op.holdsInstant op.swapped.holdsInstant
    (dateTimeComparison_swapped op) left right

end A12Kernel
