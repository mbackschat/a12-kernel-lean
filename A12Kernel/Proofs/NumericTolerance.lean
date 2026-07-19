import A12Kernel.Semantics.NumericTolerance
import A12Kernel.Proofs.NumericComparison

/-! # Fixed numeric-tolerance laws -/

namespace A12Kernel

theorem numericTolerance_threshold_pos (range : NumericToleranceRange) :
    0 < range.threshold := by
  cases range <;> decide

theorem normalizedNumericDifference_comm (left right : Rat) :
    normalizedNumericDifference left right = normalizedNumericDifference right left := by
  exact Rat.abs_sub_comm

theorem numericTolerance_holds_comm (range : NumericToleranceRange) (left right : Rat) :
    range.holds left right = range.holds right left := by
  simp [NumericToleranceRange.holds, normalizedNumericDifference_comm left right]

theorem numericTolerance_unknown_left (range : NumericToleranceRange)
    (cause : FormalCause) (right : NumericOperand) :
    range.eval (.unknown cause) right = .unknown := by
  rfl

theorem numericTolerance_unknown_right (range : NumericToleranceRange)
    (left : NumericOperand) (cause : FormalCause) :
    range.eval left (.unknown cause) = .unknown := by
  cases left <;> rfl

/-- A normalized difference exactly on the closed boundary does not fire, independently of fillability. -/
theorem numericTolerance_exactBoundary_notFired (range : NumericToleranceRange)
    (left right : Rat) (leftFill rightFill : NumericFillability)
    (boundary : normalizedNumericDifference left right = range.threshold) :
    range.eval (.value left leftFill) (.value right rightFill) = .notFired := by
  simp [NumericToleranceRange.eval, NumericToleranceRange.holds, boundary]

/-- A fixed pair outside its tolerance band always produces a value firing. -/
theorem fixedNumericToleranceFiring_is_value (range : NumericToleranceRange)
    (left right : Rat) (holds : range.holds left right = true) :
    range.eval (.value left .fixed) (.value right .fixed) = .fired .value := by
  simp [NumericToleranceRange.eval, holds, numericDifferenceFillCanClose,
    NumericFillability.fixed]

/-- When the left value is below the right, growing a grow-only left operand can close an exceeded band. -/
theorem growOnlyToleranceBelowFiring_is_omission (range : NumericToleranceRange)
    (left right : Rat) (holds : range.holds left right = true)
    (below : normalizedComparisonValue left < normalizedComparisonValue right) :
    range.eval (.value left .growOnly) (.value right .fixed) = .fired .omission := by
  simp [NumericToleranceRange.eval, holds, numericDifferenceFillCanClose,
    NumericFillability.growOnly, NumericFillability.fixed, below]

/-- A grow-only left operand cannot repair an exceeded band when it is already above the right operand. -/
theorem growOnlyToleranceNotBelowFiring_is_value (range : NumericToleranceRange)
    (left right : Rat) (holds : range.holds left right = true)
    (notBelow : ¬ normalizedComparisonValue left < normalizedComparisonValue right) :
    range.eval (.value left .growOnly) (.value right .fixed) = .fired .value := by
  simp [NumericToleranceRange.eval, holds, numericDifferenceFillCanClose,
    NumericFillability.growOnly, NumericFillability.fixed, notBelow]

/-- Swapping both operands and their fillability preserves the complete tolerance verdict. -/
theorem numericTolerance_eval_comm (range : NumericToleranceRange)
    (left right : NumericOperand) :
    range.eval left right = range.eval right left := by
  cases left with
  | unknown leftCause =>
      cases right <;> rfl
  | value leftAmount leftFill =>
      cases right with
      | unknown rightCause => rfl
      | value rightAmount rightFill =>
          cases holds : range.holds leftAmount rightAmount with
          | false =>
              have swapped : range.holds rightAmount leftAmount = false := by
                rw [← numericTolerance_holds_comm range leftAmount rightAmount]
                exact holds
              simp [NumericToleranceRange.eval, holds, swapped]
          | true =>
              have swapped : range.holds rightAmount leftAmount = true := by
                rw [← numericTolerance_holds_comm range leftAmount rightAmount]
                exact holds
              have different :
                  normalizedComparisonValue leftAmount ≠
                    normalizedComparisonValue rightAmount := by
                intro equal
                have impossible : range.threshold < 0 := by
                  simpa [NumericToleranceRange.holds, normalizedNumericDifference,
                    equal, Rat.sub_self, Rat.abs_zero] using holds
                exact (Rat.not_lt.mpr
                  (Rat.le_of_lt (numericTolerance_threshold_pos range))) impossible
              have closes := numericDifferenceFillCanClose_comm_of_ne
                leftAmount rightAmount leftFill rightFill different
              simp [NumericToleranceRange.eval, holds, swapped, closes]

end A12Kernel
