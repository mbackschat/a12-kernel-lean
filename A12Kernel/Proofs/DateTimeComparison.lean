import A12Kernel.Proofs.DateComparison
import A12Kernel.Semantics.DateTimeComparison

/-! # Resolved DateTime instant-comparison laws -/

namespace A12Kernel

/-- Resolved DateTime equality fires exactly on identical physical instants. -/
theorem dateTimeComparison_equal_iff (left right : Instant) :
    TemporalComparisonOp.equal.holdsInstant left right = true ↔ left = right := by
  simp [TemporalComparisonOp.holdsInstant]

/-- Resolved DateTime inequality fires exactly on distinct physical instants. -/
theorem dateTimeComparison_notEqual_iff (left right : Instant) :
    TemporalComparisonOp.notEqual.holdsInstant left right = true ↔ left ≠ right := by
  simp [TemporalComparisonOp.holdsInstant]

/-- Exchanging instants and the directional operator preserves every resolved comparison result. -/
theorem dateTimeComparison_swapped (op : TemporalComparisonOp)
    (left right : Instant) :
    op.swapped.holdsInstant left right = op.holdsInstant right left := by
  cases op with
  | equal => exact Bool.beq_comm
  | notEqual => exact congrArg (!·) Bool.beq_comm
  | before | beforeOrEqual | after | afterOrEqual => rfl

/-- A strict instant comparison cannot hold in both directions. -/
theorem dateTimeComparison_before_excludes_after (left right : Instant)
    (before : TemporalComparisonOp.before.holdsInstant left right = true) :
    TemporalComparisonOp.after.holdsInstant left right = false := by
  simp [TemporalComparisonOp.holdsInstant] at before ⊢
  omega

/-- Operand exchange plus the matching directional operator preserves classified DateTime verdicts and polarity. -/
theorem dateTimeComparison_eval_swapped (op : TemporalComparisonOp)
    (left right : SimpleComparisonOperand Instant) :
    op.swapped.evalInstant left right = op.evalInstant right left := by
  exact evalSymmetricComparison_swapped op.holdsInstant op.swapped.holdsInstant
    (dateTimeComparison_swapped op) left right

end A12Kernel
