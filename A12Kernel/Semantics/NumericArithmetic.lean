import A12Kernel.Semantics.NumericRounding

/-! # A12Kernel.Semantics.NumericArithmetic — precision-50 decimal arithmetic -/

namespace A12Kernel

/-- Significant-digit precision applied independently at every numeric arithmetic node. -/
def arithmeticPrecision : Nat := 50

/-- Binary arithmetic operations whose runtime value is exact arithmetic followed by the shared precision boundary. -/
inductive NumericArithmeticOp where
  | add
  | subtract
  | multiply
  deriving Repr, DecidableEq

private def decimalDigits (value : Nat) : Nat :=
  (Nat.toDigits 10 value).length

/-- Exact rational value of `10 ^ exponent`, including negative decimal exponents. -/
def decimalPower : Int → Rat
  | .ofNat exponent => (decimalFactor exponent : Nat)
  | .negSucc exponent => 1 / (decimalFactor (exponent + 1) : Nat)

/-- Base-ten order of magnitude of a nonzero rational; zero is assigned zero for totality. -/
def decimalMagnitude (value : Rat) : Int :=
  if value = 0 then
    0
  else
    let candidate := Int.subNatNat
      (decimalDigits value.num.natAbs)
      (decimalDigits value.den)
    if decimalPower candidate ≤ value.abs then candidate else candidate - 1

/-- Decimal `HALF_UP` at a signed scale; negative scales round to tens, hundreds, and so on. -/
def rescaleHalfUpSigned (value : Rat) : Int → Rat
  | .ofNat scale => rescaleHalfUp value scale
  | .negSucc exponent =>
      let factor : Rat := (decimalFactor (exponent + 1) : Nat)
      rescaleHalfUp (value / factor) 0 * factor

/-- Numeric-value account of Java `MathContext(50, HALF_UP)` over an exact rational. -/
def roundMathContext50 (value : Rat) : Rat :=
  if value = 0 then
    0
  else
    let scale : Int := (arithmeticPrecision : Int) - 1 - decimalMagnitude value
    rescaleHalfUpSigned value scale

/-- Evaluate one total binary arithmetic node and immediately apply the kernel's precision boundary. -/
def NumericArithmeticOp.eval (op : NumericArithmeticOp) (left right : Rat) : Rat :=
  roundMathContext50 <|
    match op with
    | .add => left + right
    | .subtract => left - right
    | .multiply => left * right

end A12Kernel
