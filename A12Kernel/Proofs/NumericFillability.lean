import A12Kernel.Semantics.NumericFillability
import A12Kernel.Proofs.NumericArithmetic

/-! # A12Kernel.Proofs.NumericFillability — arithmetic direction laws -/

namespace A12Kernel

theorem numericSign_ofRat_negative (value : Rat) (negative : value < 0) :
    NumericSign.ofRat value = .negative := by
  simp [NumericSign.ofRat, negative]

theorem numericSign_ofRat_zero :
    NumericSign.ofRat 0 = .zero := by
  rfl

theorem numericSign_ofRat_positive (value : Rat) (positive : 0 < value) :
    NumericSign.ofRat value = .positive := by
  have notNegative : ¬value < 0 := Rat.not_lt.mpr (Rat.le_of_lt positive)
  have nonzero : value ≠ 0 := Rat.ne_of_gt positive
  simp [NumericSign.ofRat, notNegative, nonzero]

/-- Below zero, increasing the source moves the magnitude toward zero and can therefore shrink it. -/
theorem numericFillability_absolute_negative
    (fillability : NumericFillability) :
    fillability.absolute .negative =
      { canGrow := fillability.canGrow || fillability.canShrink
        canShrink := fillability.canGrow } := by
  rfl

/-- At zero, either source direction can grow the magnitude but no filling direction can shrink it. -/
theorem numericFillability_absolute_zero
    (fillability : NumericFillability) :
    fillability.absolute .zero =
      { canGrow := fillability.canGrow || fillability.canShrink
        canShrink := false } := by
  rfl

/-- Above zero, decreasing the source is the only direction that can shrink the magnitude. -/
theorem numericFillability_absolute_positive
    (fillability : NumericFillability) :
    fillability.absolute .positive =
      { canGrow := fillability.canGrow || fillability.canShrink
        canShrink := fillability.canShrink } := by
  rfl

/-- Every value transformation preserves exactly the arithmetic-outcome availability boundary. -/
theorem numericArithmeticOutcome_mapValue_notEvaluated_iff
    (outcome : NumericArithmeticOutcome)
    (transform : Rat → NumericFillability → Rat × NumericFillability) :
    outcome.mapValue transform = .notEvaluated ↔ outcome = .notEvaluated := by
  cases outcome <;> simp [NumericArithmeticOutcome.mapValue]

/-- An operand-list selection is unavailable exactly when either operand is unavailable, before directional fillability is consulted. -/
theorem numericExtremum_selectOutcome_notEvaluated_iff
    (op : NumericExtremumOp)
    (left right : NumericArithmeticOutcome) :
    op.selectOutcome left right = .notEvaluated ↔
      left = .notEvaluated ∨ right = .notEvaluated := by
  cases left <;> cases right <;>
    simp [NumericExtremumOp.selectOutcome]

/-- At a minimum tie, both operands must be able to grow the result, while either may shrink it. -/
theorem numericFillability_minimum_tie
    (left right : NumericFillability) (amount : Rat) :
    NumericFillability.minimum left amount right amount =
      { canGrow := left.canGrow && right.canGrow
        canShrink := left.canShrink || right.canShrink } := by
  simp [NumericFillability.minimum]

/-- At a maximum tie, either operand may grow the result, while both must be able to shrink it. -/
theorem numericFillability_maximum_tie
    (left right : NumericFillability) (amount : Rat) :
    NumericFillability.maximum left amount right amount =
      { canGrow := left.canGrow || right.canGrow
        canShrink := left.canShrink && right.canShrink } := by
  simp [NumericFillability.maximum]

theorem numericArithmetic_fixed_fillability (op : NumericArithmeticOp) (left right : Rat) :
    op.fillability left .fixed right .fixed = .fixed := by
  cases op with
  | add => rfl
  | subtract => rfl
  | multiply =>
      simp only [NumericArithmeticOp.fillability]
      generalize NumericSign.ofRat left = leftSign
      generalize NumericSign.ofRat right = rightSign
      cases leftSign <;> cases rightSign <;> rfl

theorem numericFillability_add_comm (left right : NumericFillability) :
    left.add right = right.add left := by
  cases left
  cases right
  simp [NumericFillability.add, Bool.or_comm]

theorem numericFillability_subtract_eq_add_swapped (left right : NumericFillability) :
    left.subtract right = left.add right.swapDirections := by
  rfl

theorem numericFillability_subtract_fixed_right (fillability : NumericFillability) :
    fillability.subtract .fixed = fillability := by
  cases fillability
  simp [NumericFillability.subtract, NumericFillability.fixed]

theorem numericFillability_fixed_subtract (fillability : NumericFillability) :
    NumericFillability.fixed.subtract fillability = fillability.swapDirections := by
  cases fillability
  simp [NumericFillability.subtract, NumericFillability.fixed,
    NumericFillability.swapDirections]

theorem numericFillability_multiply_comm (left right : NumericFillability)
    (leftSign rightSign : NumericSign) :
    left.multiply leftSign right rightSign =
      right.multiply rightSign left leftSign := by
  rcases left with ⟨leftGrow, leftShrink⟩
  rcases right with ⟨rightGrow, rightShrink⟩
  cases leftGrow <;> cases leftShrink <;>
    cases rightGrow <;> cases rightShrink <;>
    cases leftSign <;> cases rightSign <;> rfl

theorem numericFillability_multiply_fixed_positive
    (fillability : NumericFillability) (sign : NumericSign) :
    fillability.multiply sign .fixed .positive = fillability := by
  rcases fillability with ⟨canGrow, canShrink⟩
  cases canGrow <;> cases canShrink <;> cases sign <;> rfl

theorem numericFillability_multiply_fixed_negative
    (fillability : NumericFillability) (sign : NumericSign) :
    fillability.multiply sign .fixed .negative = fillability.swapDirections := by
  rcases fillability with ⟨canGrow, canShrink⟩
  cases canGrow <;> cases canShrink <;> cases sign <;> rfl

theorem numericFillability_multiply_fixed_zero
    (fillability : NumericFillability) (sign : NumericSign) :
    fillability.multiply sign .fixed .zero = .fixed := by
  rcases fillability with ⟨canGrow, canShrink⟩
  cases canGrow <;> cases canShrink <;> cases sign <;> rfl

theorem numericArithmeticOutcome_eval_notEvaluated_left
    (op : NumericArithmeticOp) (right : NumericArithmeticOutcome) :
    NumericArithmeticOutcome.eval op .notEvaluated right = .notEvaluated := by
  rfl

theorem numericArithmeticOutcome_eval_notEvaluated_right
    (op : NumericArithmeticOp) (left : NumericArithmeticOutcome) :
    NumericArithmeticOutcome.eval op left .notEvaluated = .notEvaluated := by
  cases left <;> rfl

theorem numericArithmeticOutcome_divide_notEvaluated_left
    (right : NumericArithmeticOutcome) :
    NumericArithmeticOutcome.divide .notEvaluated right = .notEvaluated := by
  rfl

theorem numericArithmeticOutcome_divide_notEvaluated_right
    (left : NumericArithmeticOutcome) :
    NumericArithmeticOutcome.divide left .notEvaluated = .notEvaluated := by
  cases left <;> rfl

theorem numericArithmeticOutcome_divide_values_notEvaluated_iff
    (dividend divisor : Rat) (dividendFill divisorFill : NumericFillability) :
    NumericArithmeticOutcome.divide
      (.value dividend dividendFill) (.value divisor divisorFill) = .notEvaluated ↔
        divisor = 0 := by
  constructor
  · intro outcome
    by_cases zero : divisor = 0
    · exact zero
    · simp [NumericArithmeticOutcome.divide, divideNumeric, zero] at outcome
  · intro zero
    subst divisor
    rfl

theorem numericArithmeticOutcome_divide_fixed
    (dividend divisor : Rat) (nonzero : divisor ≠ 0) :
    NumericArithmeticOutcome.divide
      (.value dividend .fixed) (.value divisor .fixed) =
        .value (roundMathContext50 (dividend / divisor)) .fixed := by
  simp only [NumericArithmeticOutcome.divide, divideNumeric, if_neg nonzero]
  generalize NumericSign.ofRat dividend = dividendSign
  generalize NumericSign.ofRat divisor = divisorSign
  cases dividendSign <;> cases divisorSign <;> rfl

theorem numericArithmeticOutcome_divide_fixed_positive
    (dividend divisor : Rat) (fillability : NumericFillability)
    (positive : 0 < divisor) :
    NumericArithmeticOutcome.divide
      (.value dividend fillability) (.value divisor .fixed) =
        .value (roundMathContext50 (dividend / divisor)) fillability := by
  have nonzero : divisor ≠ 0 := Rat.ne_of_gt positive
  have divisorSign := numericSign_ofRat_positive divisor positive
  simp [NumericArithmeticOutcome.divide, divideNumeric, nonzero, divisorSign]
  generalize NumericSign.ofRat dividend = dividendSign
  cases dividendSign
  · exact numericFillability_multiply_fixed_positive fillability .negative
  · exact numericFillability_multiply_fixed_positive fillability .zero
  · exact numericFillability_multiply_fixed_positive fillability .positive

theorem numericArithmeticOutcome_divide_fixed_negative
    (dividend divisor : Rat) (fillability : NumericFillability)
    (negative : divisor < 0) :
    NumericArithmeticOutcome.divide
      (.value dividend fillability) (.value divisor .fixed) =
        .value (roundMathContext50 (dividend / divisor)) fillability.swapDirections := by
  have nonzero : divisor ≠ 0 := Ne.symm (Rat.ne_of_gt negative)
  have divisorSign := numericSign_ofRat_negative divisor negative
  simp [NumericArithmeticOutcome.divide, divideNumeric, nonzero, divisorSign]
  generalize NumericSign.ofRat dividend = dividendSign
  cases dividendSign
  · exact numericFillability_multiply_fixed_negative fillability .negative
  · exact numericFillability_multiply_fixed_negative fillability .zero
  · exact numericFillability_multiply_fixed_negative fillability .positive

theorem numericArithmeticOutcome_divide_fixed_zero_dividend
    (divisor : Rat) (divisorFill : NumericFillability) (nonzero : divisor ≠ 0) :
    NumericArithmeticOutcome.divide
      (.value 0 .fixed) (.value divisor divisorFill) = .value 0 .fixed := by
  simp only [NumericArithmeticOutcome.divide]
  rw [divideNumeric_zero_dividend divisor nonzero]
  simp only
  generalize NumericSign.ofRat divisor = divisorSign
  rcases divisorFill with ⟨canGrow, canShrink⟩
  cases canGrow <;> cases canShrink <;> cases divisorSign <;> rfl

theorem numericArithmeticOutcome_power_notEvaluated_left
    (right : NumericArithmeticOutcome) :
    NumericArithmeticOutcome.power .notEvaluated right = .notEvaluated := by
  rfl

theorem numericArithmeticOutcome_power_notEvaluated_right
    (left : NumericArithmeticOutcome) :
    NumericArithmeticOutcome.power left .notEvaluated = .notEvaluated := by
  cases left <;> rfl

theorem numericArithmeticOutcome_power_rejected_exponent
    (base exponent : Rat) (baseFill exponentFill : NumericFillability)
    (rejected : checkedPowerExponent? exponent = none) :
    NumericArithmeticOutcome.power
      (.value base baseFill) (.value exponent exponentFill) = .notEvaluated := by
  simp [NumericArithmeticOutcome.power, powerNumeric, rejected]

theorem numericArithmeticOutcome_power_values_notEvaluated_iff
    (base exponent : Rat) (baseFill exponentFill : NumericFillability) :
    NumericArithmeticOutcome.power
      (.value base baseFill) (.value exponent exponentFill) = .notEvaluated ↔
        powerNumeric base exponent = .notEvaluated := by
  unfold NumericArithmeticOutcome.power
  generalize resultEq : powerNumeric base exponent = result
  cases result <;> simp [resultEq]

theorem numericArithmeticOutcome_power_zero_exponent
    (base : Rat) (baseFill : NumericFillability) :
    NumericArithmeticOutcome.power
      (.value base baseFill) (.value 0 .fixed) = .value 1 .fixed := by
  rfl

/-- The kernel's conservative zero-base table distinguishes unsigned and signed empty exponents even though both current powers equal one. -/
theorem numericArithmeticOutcome_power_zeroBase_emptyExponent_directions :
    NumericArithmeticOutcome.power
        (.value 0 .fixed) (.value 0 .growOnly) = .value 1 .shrinkOnly ∧
      NumericArithmeticOutcome.power
        (.value 0 .fixed) (.value 0 .both) = .value 1 .growOnly := by
  decide

end A12Kernel
