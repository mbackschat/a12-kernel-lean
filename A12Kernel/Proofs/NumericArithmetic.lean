import A12Kernel.Semantics.NumericArithmetic

/-! # A12Kernel.Proofs.NumericArithmetic — laws that survive per-node decimal rounding -/

namespace A12Kernel

theorem roundMathContext50_zero :
    roundMathContext50 0 = 0 := by
  rfl

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

end A12Kernel
