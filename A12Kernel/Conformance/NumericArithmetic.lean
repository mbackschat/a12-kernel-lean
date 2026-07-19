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

private def stagedPowerBase : Rat := 473471768303411 / 10 ^ 15
private def stagedPowerResult : Rat :=
  53340688743367123920238743454888667967326752493319 / 10 ^ 52

/- Java's staged power differs from exact rational exponentiation followed by one final round. -/
example : powerNumeric stagedPowerBase 7 = .value stagedPowerResult := by
  native_decide

example : roundMathContext50 (stagedPowerBase ^ 7) =
    53340688743367123920238743454888667967326752493318 / 10 ^ 52 := by
  native_decide

private def powerSevenAtWorkingPrecision (precision : Nat) (base : Rat) : Rat :=
  let first := roundSignificantHalfUp precision base
  let squared := roundSignificantHalfUp precision (first * first)
  let cubed := roundSignificantHalfUp precision (squared * base)
  let sixth := roundSignificantHalfUp precision (cubed * cubed)
  roundMathContext50 (roundSignificantHalfUp precision (sixth * base))

private def workingPrecisionBase : Rat := 484893708568307 / 10 ^ 15

/- Exponent seven requires work precision 52; omitting X3.274's final guard digit changes the result. -/
example : positivePower workingPrecisionBase 7 =
    63026885189266057080768245915433088146473404170653 / 10 ^ 52 := by
  native_decide

example : powerSevenAtWorkingPrecision 51 workingPrecisionBase =
    63026885189266057080768245915433088146473404170654 / 10 ^ 52 := by
  native_decide

private def reciprocalFirstPowerResult : Rat :=
  37037037037037037037037037037037037037037037037036 / 10 ^ 51

/- A12 rounds the reciprocal first; taking the reciprocal after positive power is observably different. -/
example : powerNumeric 3 (-3) = .value reciprocalFirstPowerResult := by
  native_decide

example : divideNumeric 1 27 =
    .value (37037037037037037037037037037037037037037037037037 / 10 ^ 51) := by
  native_decide

example : powerNumeric 0 0 = .value 1 := by
  native_decide

example : powerNumeric 0 (-1) = .notEvaluated := by
  native_decide

example : powerNumeric 4 (-1) = .value (1 / 4) := by
  native_decide

example : powerNumeric (-2) 2 = .value 4 := by
  native_decide

example : powerNumeric (-2) 3 = .value (-8) := by
  native_decide

example : powerNumeric 2 (1 / 2) = .notEvaluated := by
  native_decide

example : powerNumeric 1 1000 = .value 1 := by
  native_decide

example : powerNumeric 1 (-1000) = .value 1 := by
  native_decide

example : powerNumeric 1 1001 = .notEvaluated := by
  native_decide

example : powerNumeric 1 (-1001) = .notEvaluated := by
  native_decide

end A12Kernel.Conformance.NumericArithmetic
