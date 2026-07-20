import A12Kernel.Semantics.NumericRounding

/-! # A12Kernel.Semantics.NumericArithmetic — precision-50 decimal arithmetic -/

namespace A12Kernel

/-- Significant-digit precision applied independently at every numeric arithmetic node. -/
def arithmeticPrecision : Nat := 50

/-- Greatest admitted absolute runtime exponent. -/
def maxPowerExponent : Nat := 1000

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

/-- Decimal significant-digit `HALF_UP`; precision zero is the exact, unlimited case. -/
def roundSignificantHalfUp (precision : Nat) (value : Rat) : Rat :=
  if precision = 0 then
    value
  else if value = 0 then
    0
  else
    let scale : Int := (precision : Int) - 1 - decimalMagnitude value
    rescaleHalfUpSigned value scale

/-- Numeric-value account of Java `MathContext(50, HALF_UP)` over an exact rational. -/
def roundMathContext50 (value : Rat) : Rat :=
  roundSignificantHalfUp arithmeticPrecision value

/-- Evaluate one total binary arithmetic node and immediately apply the kernel's precision boundary. -/
def NumericArithmeticOp.eval (op : NumericArithmeticOp) (left right : Rat) : Rat :=
  roundMathContext50 <|
    match op with
    | .add => left + right
    | .subtract => left - right
    | .multiply => left * right

/-- Result of a known-value arithmetic operation that can be semantically undefined. -/
inductive NumericArithmeticResult where
  | value (amount : Rat)
  | notEvaluated
  deriving Repr, DecidableEq

/-- Divide at precision 50; a zero divisor is explicitly not evaluated rather than Lean's rational zero. -/
def divideNumeric (dividend divisor : Rat) : NumericArithmeticResult :=
  if divisor = 0 then
    .notEvaluated
  else
    .value (roundMathContext50 (dividend / divisor))

/-- Defensive value-level admission for exactly integral exponents in the kernel's inclusive `-1000..1000` runtime range. Kernel authoring rejects fractional-scale or unknown-scale exponents; the current Lean checked consumers reject every power, while the authored scale summary records that gate for a future checked power consumer. -/
def checkedPowerExponent? (exponent : Rat) : Option Int :=
  if exponent.den = 1 then
    let integral := exponent.num
    if -(maxPowerExponent : Int) ≤ integral ∧ integral ≤ maxPowerExponent then some integral else none
  else
    none

/-- OpenJDK 21 X3.274 numeric-value algorithm for an already-admitted A12 exponent in `0..1000`. -/
def positivePower (base : Rat) (exponent : Nat) : Rat :=
  if exponent = 0 then
    1
  else
    let workPrecision := arithmeticPrecision + decimalDigits exponent + 1
    let bitIndices := (List.range (Nat.log2 exponent + 1)).reverse
    let result := bitIndices.foldl (fun accumulator bitIndex =>
      let squared := roundSignificantHalfUp workPrecision (accumulator * accumulator)
      if Nat.testBit exponent bitIndex then
        roundSignificantHalfUp workPrecision (squared * base)
      else
        squared) 1
    roundMathContext50 result

/--
Raise a known numeric value to an already-authored runtime exponent. Out-of-range integral exponents are quiet; the fractional branch is defensive totality for unchecked callers, not legal-model runtime behavior. Negative powers round the reciprocal first, before applying the positive Java power algorithm.
-/
def powerNumeric (base exponent : Rat) : NumericArithmeticResult :=
  match checkedPowerExponent? exponent with
  | none => .notEvaluated
  | some (.ofNat magnitude) => .value (positivePower base magnitude)
  | some (.negSucc predecessor) =>
      match divideNumeric 1 base with
      | .notEvaluated => .notEvaluated
      | .value reciprocal => .value (positivePower reciprocal (predecessor + 1))

end A12Kernel
