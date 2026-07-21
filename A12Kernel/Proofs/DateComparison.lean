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

/-- Formal unavailability dominates every right operand, including a valueless one. -/
theorem dateComparison_eval_unknown_left (op : DateComparisonOp)
    (cause : FormalCause) (right : SimpleComparisonOperand FullDate) :
    op.eval (.unknown cause) right = .unknown := by
  cases right <;> rfl

/-- A valueless left Date makes a comparison with a present Date not fire. -/
theorem dateComparison_eval_noValue_left (op : DateComparisonOp)
    (right : FullDate) (rightGiven : Bool) :
    op.eval .notEvaluated (.value right rightGiven) = .notFired := by
  rfl

/-- A true comparison over fixed present Dates fires with VALUE polarity. -/
theorem dateComparison_eval_fixed_firing (op : DateComparisonOp)
    (left right : FullDate) (holds : op.holds left right = true) :
    op.eval (.value left true) (.value right true) = .fired .value := by
  simp [DateComparisonOp.eval, holds]

/-- Missing provenance on either present operand makes every true Date comparison omission-typed. -/
theorem dateComparison_eval_missing_firing (op : DateComparisonOp)
    (left right : FullDate) (leftGiven rightGiven : Bool)
    (missing : (leftGiven && rightGiven) = false)
    (holds : op.holds left right = true) :
    op.eval (.value left leftGiven) (.value right rightGiven) =
      .fired .omission := by
  simp [DateComparisonOp.eval, holds, missing]

/-- Operand exchange plus the matching directional operator preserves classified comparison verdicts and polarity. -/
theorem dateComparison_eval_swapped (op : DateComparisonOp)
    (left right : SimpleComparisonOperand FullDate) :
    op.swapped.eval left right = op.eval right left := by
  cases left <;> cases right <;>
    simp [DateComparisonOp.eval, dateComparison_swapped, Bool.and_comm]

end A12Kernel
