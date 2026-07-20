import A12Kernel.Semantics.NumericArithmetic

/-! # A12Kernel.Proofs.NumericArithmetic — laws that survive per-node decimal rounding -/

namespace A12Kernel

theorem roundMathContext50_zero :
    roundMathContext50 0 = 0 := by
  rfl

theorem roundSignificantHalfUp_unlimited (value : Rat) :
    roundSignificantHalfUp 0 value = value := by
  rfl

/-- The executable A12 magnitude operation is Lean's standard rational absolute value. -/
theorem absoluteNumeric_eq_abs (value : Rat) :
    absoluteNumeric value = value.abs := by
  by_cases negative : value < 0
  · rw [Rat.abs_of_nonpos (Rat.le_of_lt negative)]
    simp [absoluteNumeric, negative]
  · rw [Rat.abs_of_nonneg (Rat.not_lt.mp negative)]
    simp [absoluteNumeric, negative]

/-- Mapping an available arithmetic value preserves exactly the availability boundary. -/
theorem numericArithmeticResult_mapValue_notEvaluated_iff
    (result : NumericArithmeticResult) (transform : Rat → Rat) :
    result.mapValue transform = .notEvaluated ↔ result = .notEvaluated := by
  cases result <;> simp [NumericArithmeticResult.mapValue]

/-- A strict full-precision ordering selects the lower or higher operand according to the operation. -/
theorem numericExtremum_selectAmount_of_lt
    (op : NumericExtremumOp) (left right : Rat) (ordered : left < right) :
    op.selectAmount left right =
      match op with
      | .minimum => left
      | .maximum => right := by
  have leftLeRight : left ≤ right := Rat.le_of_lt ordered
  have notRightLtLeft : ¬ right < left := Rat.not_lt.mpr leftLeRight
  cases op <;>
    simp [NumericExtremumOp.selectAmount, leftLeRight, notRightLtLeft]

/-- Reversing a strict full-precision ordering reverses which operand each selector retains. -/
theorem numericExtremum_selectAmount_of_gt
    (op : NumericExtremumOp) (left right : Rat) (ordered : right < left) :
    op.selectAmount left right =
      match op with
      | .minimum => right
      | .maximum => left := by
  have notLeftLeRight : ¬ left ≤ right := Rat.not_le.mpr ordered
  cases op <;>
    simp [NumericExtremumOp.selectAmount, ordered, notLeftLeRight]

/-- An operand-list arithmetic selection is unavailable exactly when either operand is unavailable. -/
theorem numericExtremum_selectArithmeticResult_notEvaluated_iff
    (op : NumericExtremumOp) (left right : NumericArithmeticResult) :
    op.selectArithmeticResult left right = .notEvaluated ↔
      left = .notEvaluated ∨ right = .notEvaluated := by
  cases left <;> cases right <;>
    simp [NumericExtremumOp.selectArithmeticResult]

theorem numericArithmetic_add_comm (left right : Rat) :
    NumericArithmeticOp.add.eval left right =
      NumericArithmeticOp.add.eval right left := by
  simp [NumericArithmeticOp.eval, Rat.add_comm]

theorem numericArithmetic_multiply_comm (left right : Rat) :
    NumericArithmeticOp.multiply.eval left right =
      NumericArithmeticOp.multiply.eval right left := by
  simp [NumericArithmeticOp.eval, Rat.mul_comm]

theorem numericArithmetic_subtract_as_add_neg (left right : Rat) :
    NumericArithmeticOp.subtract.eval left right =
      NumericArithmeticOp.add.eval left (-right) := by
  simp [NumericArithmeticOp.eval, Rat.sub_eq_add_neg]

theorem numericArithmetic_multiply_zero (value : Rat) :
    NumericArithmeticOp.multiply.eval value 0 = 0 := by
  simp [NumericArithmeticOp.eval, roundMathContext50_zero]

theorem divideNumeric_zero (dividend : Rat) :
    divideNumeric dividend 0 = .notEvaluated := by
  rfl

theorem divideNumeric_of_ne_zero (dividend divisor : Rat) (nonzero : divisor ≠ 0) :
    divideNumeric dividend divisor =
      .value (roundMathContext50 (dividend / divisor)) := by
  simp [divideNumeric, nonzero]

theorem divideNumeric_notEvaluated_iff (dividend divisor : Rat) :
    divideNumeric dividend divisor = .notEvaluated ↔ divisor = 0 := by
  simp [divideNumeric]

theorem divideNumeric_zero_dividend (divisor : Rat) (nonzero : divisor ≠ 0) :
    divideNumeric 0 divisor = .value 0 := by
  rw [divideNumeric_of_ne_zero 0 divisor nonzero, Rat.div_def, Rat.zero_mul,
    roundMathContext50_zero]

theorem positivePower_zero (base : Rat) :
    positivePower base 0 = 1 := by
  rfl

theorem powerNumeric_of_rejected_exponent (base exponent : Rat)
    (rejected : checkedPowerExponent? exponent = none) :
    powerNumeric base exponent = .notEvaluated := by
  simp [powerNumeric, rejected]

theorem powerNumeric_of_nonnegative_exponent (base exponent : Rat) (magnitude : Nat)
    (accepted : checkedPowerExponent? exponent = some (.ofNat magnitude)) :
    powerNumeric base exponent = .value (positivePower base magnitude) := by
  simp [powerNumeric, accepted]

theorem powerNumeric_zero_exponent (base : Rat) :
    powerNumeric base 0 = .value 1 := by
  rfl

theorem powerNumeric_zero_negative_exponent (exponent : Rat) (predecessor : Nat)
    (accepted : checkedPowerExponent? exponent = some (.negSucc predecessor)) :
    powerNumeric 0 exponent = .notEvaluated := by
  simp [powerNumeric, accepted, divideNumeric]

theorem powerNumeric_negative_exponent (base exponent : Rat) (predecessor : Nat)
    (accepted : checkedPowerExponent? exponent = some (.negSucc predecessor))
    (nonzero : base ≠ 0) :
    powerNumeric base exponent =
      .value (positivePower (roundMathContext50 (1 / base)) (predecessor + 1)) := by
  simp [powerNumeric, accepted, divideNumeric, nonzero]

end A12Kernel
