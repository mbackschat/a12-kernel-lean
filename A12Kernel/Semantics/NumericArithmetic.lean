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

namespace NumericArithmeticOp

/-- Static result scale for one node over two direct Number fields: the additive nodes take the larger operand scale, while multiplication sums them. Shared by the target-owning binary computation and by an operand-local field pair inside operand-list extrema. -/
def directFieldResultScale (op : NumericArithmeticOp)
    (left right : Nat) : Nat :=
  match op with
  | .add | .subtract => max left right
  | .multiply => left + right

end NumericArithmeticOp

/-- Numeric operand-list selectors. The source operation is nonempty and evaluates operands in authored order. -/
inductive NumericExtremumOp where
  | minimum
  | maximum
  deriving Repr, DecidableEq

namespace NumericExtremumOp

/-- Select one of two known values at full rational precision. On an equal pair, `Min` retains the left value while `Max` retains the right, matching the source fold even though this reduced amount domain cannot observe origin identity. -/
def selectAmount (op : NumericExtremumOp) (left right : Rat) : Rat :=
  match op with
  | .minimum => if left ≤ right then left else right
  | .maximum => if left > right then left else right

end NumericExtremumOp

/-- Decimal digit count, zero counting as one digit. The binary length fixes the count to one of three candidates, so two powers of ten decide it; `Nat.toDigits` is quadratic in the digit count (31 s for 300,000 digits on 2026-11-12), which a power result such as `10 ^ (3·10^6)` cannot afford. The rational constant is below `log10 2` by less than `10^-19`, so the candidates stay correct for any binary length below `10^18`. -/
private def decimalDigits (value : Nat) : Nat :=
  let estimate := Nat.log2 value * 3010299956639811952 / 10000000000000000000 + 1
  estimate + (if 10 ^ estimate ≤ value then 1 else 0) + (if 10 ^ (estimate + 1) ≤ value then 1 else 0)

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

/-- Exact numeric magnitude before any consumer-specific metadata projection. -/
def absoluteNumeric (value : Rat) : Rat :=
  if value < 0 then -value else value

/-- Transform only an available arithmetic value; unavailability remains unavailable. -/
def NumericArithmeticResult.mapValue (result : NumericArithmeticResult)
    (transform : Rat → Rat) : NumericArithmeticResult :=
  match result with
  | .value amount => .value (transform amount)
  | .notEvaluated => .notEvaluated

/-- Apply a decimal rounding wrapper without turning an unavailable numeric value into zero. -/
def NumericArithmeticResult.round (result : NumericArithmeticResult)
    (mode : DecimalRoundingMode) (places : RoundingPlaces) : NumericArithmeticResult :=
  result.mapValue (fun amount => roundDecimal mode amount places)

/-- Apply absolute value without turning an unavailable numeric value into zero. -/
def NumericArithmeticResult.absolute
    (result : NumericArithmeticResult) : NumericArithmeticResult :=
  result.mapValue absoluteNumeric

/-- Combine two already-evaluated operand-list values; either unavailable operand makes the selector unavailable. -/
def NumericExtremumOp.selectArithmeticResult (op : NumericExtremumOp) :
    NumericArithmeticResult → NumericArithmeticResult → NumericArithmeticResult
  | .value left, .value right => .value (op.selectAmount left right)
  | _, _ => .notEvaluated

/-- Divide at precision 50; a zero divisor is explicitly not evaluated rather than Lean's rational zero. -/
def divideNumeric (dividend divisor : Rat) : NumericArithmeticResult :=
  if divisor = 0 then
    .notEvaluated
  else
    .value (roundMathContext50 (dividend / divisor))

/-- Defensive value-level admission for exactly integral exponents in the kernel's inclusive `-1000..1000` runtime range. Kernel authoring rejects fractional-scale or unknown-scale exponents, so the fractional branch is reached only by unchecked callers. -/
def checkedPowerExponent? (exponent : Rat) : Option Int :=
  if exponent.den = 1 then
    let integral := exponent.num
    if -(maxPowerExponent : Int) ≤ integral ∧ integral ≤ maxPowerExponent then some integral else none
  else
    none

/-- The host decimal arithmetic raised because a scale left its signed 32-bit range ([spec/04 §3](../../spec/04-numbers-and-decimals.md#3-arithmetic-domain-failures-are-consumer-sensitive)). The host names it an overflow or an underflow only in message text, which the theory does not keep. -/
inductive HostScaleRangeFailure where
  | outOfRange
  deriving Repr, DecidableEq

/-- Bounds of the host's signed 32-bit decimal scale. -/
def hostScaleMin : Int := -2147483648

def hostScaleMax : Int := 2147483647

/-- A decimal as the host's decimal arithmetic holds it, `unscaled × 10 ^ (-scale)`. Unlike a rational value it keeps a scale, and power's range check reads that scale. -/
structure HostDecimal where
  unscaled : Int
  scale : Int
  deriving Repr, DecidableEq

/-- Exponent of the largest power of `factor` dividing a positive `value`. The powers `factor ^ 2 ^ j` that divide it are collected by squaring and then removed from the largest down, so a value of millions of digits needs only logarithmically many divisions. -/
private def multiplicity (factor value : Nat) : Nat :=
  let rec dividingPowers : Nat → Nat → Nat → List (Nat × Nat) → List (Nat × Nat)
    | 0, _, _, found => found
    | fuel + 1, power, width, found =>
        if power ≤ value ∧ value % power = 0 then
          dividingPowers fuel (power * power) (2 * width) ((power, width) :: found)
        else found
  if factor < 2 ∨ value = 0 then 0 else
    ((dividingPowers (Nat.log2 value + 1) factor 1 []).foldl
      (fun (rest, count) (power, width) =>
        if rest % power = 0 then (rest / power, count + width) else (rest, count))
      (value, 0)).2

/-- Count of trailing decimal zeros of a positive `value`. A value carrying at most 100 significant digits, as every evaluated amount does after the precision-50 boundary, is settled by one division; others take the general count. -/
private def trailingDecimalZeros (value : Nat) : Nat :=
  let digits := decimalDigits value
  if 120 < digits then
    let shift := digits - 100
    if value % decimalFactor shift = 0 then
      shift + multiplicity 10 (value / decimalFactor shift)
    else multiplicity 10 value
  else multiplicity 10 value

namespace HostDecimal

/-- The exact rational value. -/
def toRat (decimal : HostDecimal) : Rat :=
  if decimal.scale ≤ 0 then
    ((decimal.unscaled * (decimalFactor (-decimal.scale).toNat : Nat) : Int) : Rat)
  else
    mkRat decimal.unscaled (decimalFactor decimal.scale.toNat)

/-- The shortest decimal form of a finite decimal, `none` for another rational. -/
def ofFiniteDecimal? (value : Rat) : Option HostDecimal :=
  if value.num = 0 then some ⟨0, 0⟩
  else if value.den = 1 then
    let zeros := trailingDecimalZeros value.num.natAbs
    some ⟨value.num / (decimalFactor zeros : Int), -(zeros : Int)⟩
  else
    let twos := multiplicity 2 value.den
    let fives := multiplicity 5 value.den
    if value.den = 2 ^ twos * 5 ^ fives then
      let scale := max twos fives
      some ⟨value.num * ((2 ^ (scale - twos) * 5 ^ (scale - fives) : Nat) : Int), scale⟩
    else none

/--
The host form a power reads its base in. The host keeps a value's trailing zeros, which a rational value has lost, so the scales this form gives every later product can differ from the host's by up to the working precision per factor; spec/04 §3 bounds that band. A rational that is no finite decimal is unreachable from evaluation, where every division rounds; it takes its precision-50 rounding for totality.
-/
def ofRat (value : Rat) : HostDecimal :=
  (ofFiniteDecimal? value).getD ((ofFiniteDecimal? (roundMathContext50 value)).getD ⟨0, 0⟩)

/-- `HALF_UP` division of a signed coefficient by `10 ^ drop`; exact ties round away from zero. -/
private def dropDigitsHalfUp (unscaled : Int) (drop : Nat) : Int :=
  let factor := decimalFactor drop
  let magnitude := unscaled.natAbs
  let rounded := magnitude / factor + (if factor ≤ 2 * (magnitude % factor) then 1 else 0)
  if unscaled < 0 then -(rounded : Int) else rounded

/-- Round to `precision` significant digits as the host does: each dropped digit lowers the scale, a rounding carry drops one more, and a scale falling below the range raises. The value is `roundSignificantHalfUp precision` of the input's value. -/
def roundToPrecision (precision : Nat) (decimal : HostDecimal) :
    Except HostScaleRangeFailure HostDecimal :=
  let digits := decimalDigits decimal.unscaled.natAbs
  if digits ≤ precision then .ok decimal else
    let drop := digits - precision
    let rounded := dropDigitsHalfUp decimal.unscaled drop
    let (rounded, drop) :=
      if precision < decimalDigits rounded.natAbs then (rounded / 10, drop + 1) else (rounded, drop)
    let scale := decimal.scale - drop
    if hostScaleMin ≤ scale then .ok ⟨rounded, scale⟩ else .error .outOfRange

/-- The host's product at a working precision. Its scale, the sum of both scales, is checked before rounding; a zero left factor clamps it instead of raising. -/
def multiplyRounded (precision : Nat) (left right : HostDecimal) :
    Except HostScaleRangeFailure HostDecimal :=
  let scale := left.scale + right.scale
  if hostScaleMin ≤ scale ∧ scale ≤ hostScaleMax then
    roundToPrecision precision ⟨left.unscaled * right.unscaled, scale⟩
  else if left.unscaled = 0 then
    .ok ⟨0, if 0 < scale then hostScaleMax else hostScaleMin⟩
  else .error .outOfRange

/-- OpenJDK 21's X3.274 `BigDecimal.pow` at precision 50, `HALF_UP`, for an exponent in `1..1000`: from the top bit down, multiply by the base when the bit is set and square before every lower bit, each at `50 + d + 1` digits with `d` the exponent's digit count, then round to 50. -/
def power (base : HostDecimal) (exponent : Nat) : Except HostScaleRangeFailure HostDecimal := do
  let workPrecision := arithmeticPrecision + decimalDigits exponent + 1
  let top := Nat.log2 exponent
  let mut accumulator : HostDecimal := ⟨1, 0⟩
  for step in List.range (top + 1) do
    let bitIndex := top - step
    if exponent.testBit bitIndex then
      accumulator ← multiplyRounded workPrecision accumulator base
    if bitIndex ≠ 0 then
      accumulator ← multiplyRounded workPrecision accumulator accumulator
  roundToPrecision arithmeticPrecision accumulator

end HostDecimal

/-- Positive power on the host's decimal form, with its value as a rational; zero exponent is one. -/
def positivePower (base : Rat) (exponent : Nat) : Except HostScaleRangeFailure Rat :=
  if exponent = 0 then .ok 1 else HostDecimal.toRat <$> (HostDecimal.ofRat base).power exponent

/--
Raise a known numeric value to an already-authored runtime exponent, keeping the host's scale-range raise apart. Out-of-range integral exponents are quiet; the fractional branch is defensive totality for unchecked callers, not legal-model runtime behavior. Negative powers round the reciprocal first, before applying the positive Java power algorithm. The validation comparison reads the raise from here ([spec/10 §3.1](../../spec/10-validation-and-polarity.md#31-truth-testing-and-message-classification)).
-/
def powerChecked (base exponent : Rat) : Except HostScaleRangeFailure NumericArithmeticResult :=
  match checkedPowerExponent? exponent with
  | none => .ok .notEvaluated
  | some (.ofNat magnitude) => NumericArithmeticResult.value <$> positivePower base magnitude
  | some (.negSucc predecessor) =>
      match divideNumeric 1 base with
      | .notEvaluated => .ok .notEvaluated
      | .value reciprocal => NumericArithmeticResult.value <$> positivePower reciprocal (predecessor + 1)

/-- Power without the raise: a scale-range raise has no value, which a computation's target receives exactly as a domain failure (measured, spec/04 §3). A consumer that must tell the raise apart reads `powerChecked`. -/
def powerNumeric (base exponent : Rat) : NumericArithmeticResult :=
  match powerChecked base exponent with
  | .ok result => result
  | .error _ => .notEvaluated

end A12Kernel
