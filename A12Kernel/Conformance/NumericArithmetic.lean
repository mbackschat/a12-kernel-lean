import A12Kernel.Semantics.NumericArithmetic

/-! # Precision-50 numeric-arithmetic separating cases -/

namespace A12Kernel.Conformance.NumericArithmetic

open A12Kernel

private def tenPow50 : Rat := 10 ^ 50

example : decimalMagnitude (tenPow50 - 1) = 49 := by
  native_decide

example : decimalMagnitude tenPow50 = 50 := by
  native_decide

/- Addition and subtraction round at their own AST node; they are not exact above 50 significant digits. -/
example : NumericArithmeticOp.add.eval (tenPow50 - 1) (3 / 5) = tenPow50 := by
  native_decide

example : NumericArithmeticOp.subtract.eval tenPow50 (2 / 5) = tenPow50 := by
  native_decide

/- A 52-digit product is rounded to 50 significant digits, not to 50 fractional places. -/
example : NumericArithmeticOp.multiply.eval (10 ^ 26 - 1) (10 ^ 26 - 1) =
    10 ^ 52 - 2 * 10 ^ 26 := by
  native_decide

private def tinyTie : Rat := (10 ^ 50 + 5) / 10 ^ 60
private def tinyTieRounded : Rat := (10 ^ 49 + 1) / 10 ^ 59

/- Significant-digit rounding also chooses a positive fractional scale for small magnitudes. -/
example : roundMathContext50 tinyTie = tinyTieRounded := by
  native_decide

/- `HALF_UP` sends a negative tie away from zero. -/
example : roundMathContext50 (-tinyTie) = -tinyTieRounded := by
  native_decide

example : NumericArithmeticOp.add.eval (12 / 10) (23 / 10) = 35 / 10 := by
  native_decide

example : divideNumeric 1 0 = .notEvaluated := by
  rfl

private def repeatingThird50Coefficient : Nat := (10 ^ 50 - 1) / 3
private def repeatingThird50 : Rat := repeatingThird50Coefficient / 10 ^ 50

example : divideNumeric 1 3 = .value repeatingThird50 := by
  native_decide

example : divideNumeric (-1) 3 = .value (-repeatingThird50) := by
  native_decide

example : divideNumeric 1 (-3) = .value (-repeatingThird50) := by
  native_decide

/- Precision counts all digits: this quotient has 20 integer and 30 fractional digits. -/
example : divideNumeric (10 ^ 20) 3 =
    .value (repeatingThird50Coefficient / 10 ^ 30) := by
  native_decide

example : divideNumeric 0 7 = .value 0 := by
  native_decide

/- The rounded quotient is consumed as-is by the following multiplication node. -/
example : NumericArithmeticOp.multiply.eval repeatingThird50 3 =
    1 - 1 / 10 ^ 50 := by
  native_decide

/- Per-node precision makes arithmetic non-associative. -/
example :
    NumericArithmeticOp.add.eval (NumericArithmeticOp.add.eval tenPow50 (-tenPow50)) (3 / 5) =
      3 / 5 := by
  native_decide

example :
    NumericArithmeticOp.add.eval tenPow50 (NumericArithmeticOp.add.eval (-tenPow50) (3 / 5)) =
      1 := by
  native_decide

end A12Kernel.Conformance.NumericArithmetic
