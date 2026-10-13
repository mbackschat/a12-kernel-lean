import A12Kernel.Semantics.NumericInput

/-! # Number declaration bounds through binary64

A Number declaration's `minValue` and `maxValue` are authored as exact decimals, but the Kernel
carries them through Java `double` twice ([spec/04](../../spec/04-numbers-and-decimals.md)). The
model consistency check compares the nearest double against a double limit, so a bound one digit past
the limit can pass ([checkpoint](../../docs/sources/domain-ingestion-probes.md#src-number-declaration-bounds-k17)). Generated code then receives the bound as text printed from that double, and
the runtime checks a stored value against that text, not against the authored decimal.

This module owns the binary64 arithmetic both uses need, over exact rationals: correctly rounded
conversion, the shortest decimal that reads back to a double, and the two printed forms. Doubles
outside the normal range are reported as beyond the represented profile rather than modelled.
-/

namespace A12Kernel.NumberBound

private def pow2 (exponent : Int) : Rat :=
  if 0 ≤ exponent then ((2 ^ exponent.toNat : Nat) : Rat) else 1 / ((2 ^ exponent.natAbs : Nat) : Rat)

private def magnitude (q : Rat) : Rat := if q < 0 then -q else q

private def pow10 (exponent : Int) : Rat :=
  if 0 ≤ exponent then ((10 ^ exponent.toNat : Nat) : Rat) else 1 / ((10 ^ exponent.natAbs : Nat) : Rat)

/-- The largest `k` with `base ^ k ≤ q`, for a positive `q`. The digit-length estimate is within one
of the answer, so a bounded correction settles it. -/
private def floorLog (power : Int → Rat) (estimate : Rat → Int) (q : Rat) : Int := Id.run do
  let mut k := estimate q
  for _ in [0:4] do
    if q < power k then k := k - 1
    else if power (k + 1) ≤ q then k := k + 1
  pure k

private def floorLog2 (q : Rat) : Int :=
  floorLog pow2 (fun q => (q.num.natAbs.log2 : Int) - q.den.log2) q

private def floorLog10 (q : Rat) : Int :=
  floorLog pow10 (fun q => ((toString q.num.natAbs).length : Int) - (toString q.den).length) q

/-- A positive finite double `mantissa · 2 ^ exponent` with a 53-bit mantissa. -/
structure Double where
  mantissa : Nat
  exponent : Int
  deriving Repr, DecidableEq

def Double.value (double : Double) : Rat := double.mantissa * pow2 double.exponent

/-- The double nearest a positive rational, ties to an even mantissa, or `none` when the result would
be subnormal or overflow; neither case is represented. -/
def nearestPositive? (q : Rat) : Option Double :=
  let exponent := floorLog2 q - 52
  let scaled := q / pow2 exponent
  let floor := scaled.floor.toNat
  let remainder := scaled - floor
  let rounded := if 1 / 2 < remainder || (remainder = 1 / 2 && floor % 2 = 1) then floor + 1 else floor
  let (mantissa, exponent) := if rounded = 2 ^ 53 then (2 ^ 52, exponent + 1) else (rounded, exponent)
  if exponent + 52 < -1022 || 1023 < exponent + 52 then none else some { mantissa, exponent }

/-- Java `BigDecimal.doubleValue`, as the exact value of the double: correctly rounded, the sign
carried through. Zero stays zero; a `BigDecimal` has no negative zero to carry. -/
def nearest? (q : Rat) : Option Rat :=
  if q = 0 then some 0
  else (nearestPositive? (magnitude q)).map fun double => if q < 0 then -double.value else double.value

/-- The decimal `coefficient · 10 ^ exponent` that Java 21's `Double.toString` selects for a positive
double: among the decimals that read back to it, one with the fewest significant digits, the closest
of those, and the one with an even last digit on a tie. The rounding interval's ends belong to it
exactly when the mantissa is even, because a tie reads back to the even neighbour. The JDK's extra
two-digit candidates for a one-digit result change nothing for a normal double, whose interval is
narrower than one unit of a second significant digit. -/
def shortestPositive (double : Double) : Int × Int := Id.run do
  let value := double.value
  let ulp := pow2 double.exponent
  let below := if double.mantissa = 2 ^ 52 then ulp / 2 else ulp
  let low := value - below / 2
  let high := value + ulp / 2
  let closed := double.mantissa % 2 = 0
  let inside (candidate : Rat) : Bool :=
    if closed then low ≤ candidate && candidate ≤ high else low < candidate && candidate < high
  let top := floorLog10 value + 1
  let mut result : Int × Int := (0, 0)
  -- The coarsest decimal step holding a candidate gives the fewest significant digits: a candidate on
  -- a coarser step would have been found first. Seventeen digits always suffice for a double.
  for offset in [0:20] do
    let exponent := top - offset
    let step := pow10 exponent
    let first := (low / step).ceil
    let last := (high / step).floor
    let count := (last - first + 1).toNat
    let candidates : List Int := ((List.range count).map (fun (index : Nat) => first + (index : Int))).filter
      (fun coefficient => inside ((coefficient : Rat) * step))
    let closer (best? : Option Int) (coefficient : Int) : Option Int := match best? with
      | none => some coefficient
      | some best =>
          let distance := magnitude ((coefficient : Rat) * step - value)
          let bestDistance := magnitude ((best : Rat) * step - value)
          if distance < bestDistance || (distance = bestDistance && coefficient % 2 = 0) then
            some coefficient
          else some best
    if let some best := candidates.foldl closer none then
      result := (best, exponent)
      break
  pure result

/-- Plain text of `coefficient · 10 ^ exponent` with a given number of fraction digits, the minus
written whenever `negative` holds, including on a zero coefficient. -/
private def render (negative : Bool) (units : Nat) (fractionDigits : Nat) : String :=
  let digits := (toString units).toList
  let padded := List.replicate (fractionDigits + 1 - min digits.length (fractionDigits + 1)) '0' ++ digits
  let integer := padded.take (padded.length - fractionDigits)
  let fraction := padded.drop (padded.length - fractionDigits)
  (if negative then "-" else "") ++ String.ofList integer ++
    (if fractionDigits = 0 then "" else "." ++ String.ofList fraction)

/-- The bound text generated code receives, printed from the double nearest the authored bound. A
declaration fixing its fraction digits, `minFractionalDigits = maxFractionalDigits ≥ 0`, prints them
with Java's `%.nf`, which rounds the shortest decimal's digits half up, so `0.125` prints `0.13` and a
small negative prints `-0.00`; any other declaration prints the shortest decimal plainly, without
trailing zeros ([checkpoint](../../docs/sources/domain-ingestion-probes.md#src-number-declaration-bounds-k17)). -/
def printed? (authored : Rat) (minFractionalDigits maxFractionalDigits : Int) : Option String := do
  let value ← nearest? authored
  let negative := value < 0
  let (coefficient, exponent) ← if value = 0 then pure ((0 : Int), (0 : Int)) else
    (nearestPositive? (magnitude value)).map shortestPositive
  let fixed := minFractionalDigits = maxFractionalDigits && 0 ≤ minFractionalDigits
  if fixed then
    let digits := minFractionalDigits.toNat
    let scaled := (coefficient : Rat) * pow10 (exponent + digits)
    let rounded := (scaled + 1 / 2).floor.toNat
    pure (render negative rounded digits)
  else
    let fractionDigits := if exponent < 0 then exponent.natAbs else 0
    let units := (coefficient * (10 ^ (if 0 ≤ exponent then exponent.toNat else 0) : Nat)).toNat
    pure (render (negative && value ≠ 0) units fractionDigits)

/-- The bound a stored value is compared against: the printed text read back as a decimal, as the
runtime reads it. -/
def printedValue? (authored : Rat) (minFractionalDigits maxFractionalDigits : Int) : Option Rat :=
  (printed? authored minFractionalDigits maxFractionalDigits).bind fun text =>
    (parseNumericFormalRead? text).map (·.value)

/-- Java `Math.pow(10, 15 - m) - Math.pow(10, -m)` in double, the largest magnitude a bound may have at
`m` fraction digits. Both powers are taken as the correctly rounded doubles. -/
def maximumAllowed (maxFractionalDigits : Int) : Rat :=
  let power (exponent : Int) := (nearest? (pow10 exponent)).getD 0
  (nearest? (power (15 - maxFractionalDigits) - power (-maxFractionalDigits))).getD 0

/-- Whether the model check refuses a `maxValue` (`minimum = false`) or a `minValue`: the authored
bound's nearest double exceeds the double limit, a minimum by magnitude. A bound beyond the normal
double range needs no rounding to decide: an overflow is an infinity, which exceeds the limit unless it
is a negative maximum, and a subnormal magnitude is far below any limit. -/
def exceedsLimit (authored : Rat) (maxFractionalDigits : Int) (minimum : Bool) : Bool :=
  match nearest? authored with
  | some value => maximumAllowed maxFractionalDigits < (if minimum then magnitude value else value)
  | none => 1 ≤ magnitude authored && (minimum || 0 < authored)

end A12Kernel.NumberBound
