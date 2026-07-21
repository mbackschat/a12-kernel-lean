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

/-- A true comparison over clean typed DateTime observations delegates to the existing fixed-value verdict law. -/
theorem dateTimeComparison_evalObserved_clean_firing (op : TemporalComparisonOp)
    (left right : Instant) (holds : op.holdsInstant left right = true) :
    op.evalInstantObserved (.value left) (.value right) = .fired .value := by
  exact evalSymmetricComparison_fixed_firing op.holdsInstant left right holds

/-- Typed DateTime emptiness retains the exact-instant comparison's no-value behavior. -/
theorem dateTimeComparison_evalObserved_empty_left (op : TemporalComparisonOp)
    (right : Instant) :
    op.evalInstantObserved .empty (.value right) = .notFired := by
  exact evalSymmetricComparison_noValue_left op.holdsInstant right true

/-- Typed DateTime unavailability remains UNKNOWN through the shared observation classifier. -/
theorem dateTimeComparison_evalObserved_unknown_left (op : TemporalComparisonOp)
    (cause : FormalCause) (right : CellObservation Instant) :
    op.evalInstantObserved (.unknown cause) right = .unknown := by
  exact evalSymmetricComparison_unknown_left op.holdsInstant cause
    right.asValidationSimpleOperand

end A12Kernel
