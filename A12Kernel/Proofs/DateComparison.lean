import A12Kernel.Proofs.FullDate
import A12Kernel.Proofs.ScalarEquality
import A12Kernel.Semantics.DateComparison

/-! # Resolved full-Date comparison laws -/

namespace A12Kernel

/-- Resolved Date equality fires exactly on identical calendar values. -/
theorem dateComparison_equal_iff (left right : FullDate) :
    TemporalComparisonOp.equal.holds left right = true ↔ left = right := by
  simp [TemporalComparisonOp.holds]

/-- Resolved Date inequality fires exactly on distinct calendar values. -/
theorem dateComparison_notEqual_iff (left right : FullDate) :
    TemporalComparisonOp.notEqual.holds left right = true ↔ left ≠ right := by
  simp [TemporalComparisonOp.holds]

/-- Exchanging operands and the directional operator preserves every resolved comparison result. -/
theorem dateComparison_swapped (op : TemporalComparisonOp)
    (left right : FullDate) :
    op.swapped.holds left right = op.holds right left := by
  cases op with
  | equal => exact Bool.beq_comm
  | notEqual => exact congrArg (!·) Bool.beq_comm
  | before | beforeOrEqual | after | afterOrEqual => rfl

/-- A strict Date comparison cannot hold in both directions. -/
theorem dateComparison_before_excludes_after (left right : FullDate)
    (before : TemporalComparisonOp.before.holds left right = true) :
    TemporalComparisonOp.after.holds left right = false := by
  simp only [TemporalComparisonOp.holds] at before ⊢
  cases reverse : right.before left with
  | false => rfl
  | true =>
      exact False.elim
        ((civilDate_before_asymmetric _ _
          ((fullDate_before_iff left right).mp before))
          ((fullDate_before_iff right left).mp reverse))

/-- Formal unavailability dominates every right operand, including a valueless one. -/
theorem dateComparison_eval_unknown_left (op : TemporalComparisonOp)
    (cause : FormalCause) (right : SimpleComparisonOperand FullDate) :
    op.eval (.unknown cause) right = .unknown := by
  exact evalSymmetricComparison_unknown_left op.holds cause right

/-- A valueless left Date makes a comparison with a present Date not fire. -/
theorem dateComparison_eval_noValue_left (op : TemporalComparisonOp)
    (right : FullDate) (rightGiven : Bool) :
    op.eval .notEvaluated (.value right rightGiven) = .notFired := by
  exact evalSymmetricComparison_noValue_left op.holds right rightGiven

/-- A true comparison over fixed present Dates fires with VALUE polarity. -/
theorem dateComparison_eval_fixed_firing (op : TemporalComparisonOp)
    (left right : FullDate) (holds : op.holds left right = true) :
    op.eval (.value left true) (.value right true) = .fired .value := by
  exact evalSymmetricComparison_fixed_firing op.holds left right holds

/-- Missing provenance on either present operand makes every true Date comparison omission-typed. -/
theorem dateComparison_eval_missing_firing (op : TemporalComparisonOp)
    (left right : FullDate) (leftGiven rightGiven : Bool)
    (missing : (leftGiven && rightGiven) = false)
    (holds : op.holds left right = true) :
    op.eval (.value left leftGiven) (.value right rightGiven) =
      .fired .omission := by
  exact evalSymmetricComparison_missing_firing op.holds left right
    leftGiven rightGiven missing holds

/-- Operand exchange plus the matching directional operator preserves classified comparison verdicts and polarity. -/
theorem dateComparison_eval_swapped (op : TemporalComparisonOp)
    (left right : SimpleComparisonOperand FullDate) :
    op.swapped.eval left right = op.eval right left := by
  exact evalSymmetricComparison_swapped op.holds op.swapped.holds
    (dateComparison_swapped op) left right

/-- A true comparison over two clean typed observations delegates to the existing fixed-value verdict law. -/
theorem dateComparison_evalObserved_clean_firing (op : TemporalComparisonOp)
    (left right : FullDate) (holds : op.holds left right = true) :
    op.evalObserved (.value left) (.value right) = .fired .value := by
  exact dateComparison_eval_fixed_firing op left right holds

/-- Typed validation emptiness retains the Date comparison's no-value behavior. -/
theorem dateComparison_evalObserved_empty_left (op : TemporalComparisonOp)
    (right : FullDate) :
    op.evalObserved .empty (.value right) = .notFired := by
  exact dateComparison_eval_noValue_left op right true

/-- Typed validation unavailability retains its exact cause until the existing verdict projection hides it as UNKNOWN. -/
theorem dateComparison_evalObserved_unknown_left (op : TemporalComparisonOp)
    (cause : FormalCause) (right : CellObservation FullDate) :
    op.evalObserved (.unknown cause) right = .unknown := by
  exact dateComparison_eval_unknown_left op cause right.asValidationSimpleOperand

end A12Kernel
