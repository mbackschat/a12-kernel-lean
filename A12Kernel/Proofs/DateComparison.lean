import A12Kernel.Proofs.FullDate
import A12Kernel.Semantics.DateComparison

/-! # Resolved full-Date comparison laws -/

namespace A12Kernel

/-- Resolved Date equality fires exactly on identical calendar values. -/
theorem dateComparison_equal_iff (left right : FullDate) :
    DateComparisonOp.equal.holds left right = true ↔ left = right := by
  simp [DateComparisonOp.holds]

/-- Resolved Date inequality fires exactly on distinct calendar values. -/
theorem dateComparison_notEqual_iff (left right : FullDate) :
    DateComparisonOp.notEqual.holds left right = true ↔ left ≠ right := by
  simp [DateComparisonOp.holds]

/-- Exchanging operands and the directional operator preserves every resolved comparison result. -/
theorem dateComparison_swapped (op : DateComparisonOp)
    (left right : FullDate) :
    op.swapped.holds left right = op.holds right left := by
  cases op with
  | equal => exact Bool.beq_comm
  | notEqual => exact congrArg (!·) Bool.beq_comm
  | before | beforeOrEqual | after | afterOrEqual => rfl

/-- A strict Date comparison cannot hold in both directions. -/
theorem dateComparison_before_excludes_after (left right : FullDate)
    (before : DateComparisonOp.before.holds left right = true) :
    DateComparisonOp.after.holds left right = false := by
  simp only [DateComparisonOp.holds] at before ⊢
  cases reverse : right.before left with
  | false => rfl
  | true =>
      exact False.elim
        ((civilDate_before_asymmetric _ _
          ((fullDate_before_iff left right).mp before))
          ((fullDate_before_iff right left).mp reverse))

end A12Kernel
