import A12Kernel.Semantics.NumericRounding

/-! # Stored Number representation

Numeric expressions remain exact rational values. This capsule owns their scale-19 store pre-round and conversion into the exact decimal form used at a Number target. Target admission, validation, delta projection, and document application remain separate.
-/

namespace A12Kernel

/-- Exact stored decimal representation. Unlike `Rat`, the coefficient and scale preserve `7` versus `7.00`. -/
structure StoredNumber where
  unscaled : Int
  scale : Nat
  deriving Repr, DecidableEq

namespace StoredNumber

private def zeros (count : Nat) : String :=
  String.ofList (List.replicate count '0')

private def renderMagnitude (magnitude scale : Nat) : String :=
  let digits := toString magnitude
  if scale = 0 then
    digits
  else if digits.length ≤ scale then
    "0." ++ zeros (scale - digits.length) ++ digits
  else
    let wholeLength := digits.length - scale
    String.ofList (digits.toList.take wholeLength) ++ "." ++
      String.ofList (digits.toList.drop wholeLength)

/-- Normalized dot-decimal stored text with exactly `scale` fractional digits. Model-configured output materialization is a later boundary. -/
def render (value : StoredNumber) : String :=
  let unsigned := renderMagnitude value.unscaled.natAbs value.scale
  if value.unscaled < 0 then "-" ++ unsigned else unsigned

/-- Numeric value represented by the stored coefficient and scale. -/
def amount (value : StoredNumber) : Rat :=
  (value.unscaled : Rat) / (decimalFactor value.scale : Nat)

/-- Count stored digits exactly as the universal Number check does: omit the sign and decimal separator, retain every zero. -/
def digitCount (value : StoredNumber) : Nat :=
  max (toString value.unscaled.natAbs).length (value.scale + 1)

/-- Remove only coefficient zeroes that correspond to fractional places, returning the reduced coefficient and natural scale. -/
def stripFractionalZeros : Nat → Nat → Nat × Nat
  | magnitude, 0 => (magnitude, 0)
  | magnitude, scale + 1 =>
      if magnitude % 10 = 0 then
        stripFractionalZeros (magnitude / 10) scale
      else
        (magnitude, scale + 1)

/-- Apply the store-time scale-19 `HALF_UP` boundary, strip only fractional trailing zeros, then pad to the requested minimum scale. The first result is the natural fractional scale before padding. -/
def fromComputed (amount : Rat) (minimumScale : Nat) : Nat × StoredNumber :=
  let scaled :=
    rescaleHalfUpUnscaled amount decimalPreRoundScale
  let (magnitude, naturalScale) :=
    stripFractionalZeros scaled.natAbs decimalPreRoundScale
  let storedScale := max naturalScale minimumScale
  let storedMagnitude :=
    magnitude * decimalFactor (storedScale - naturalScale)
  let unscaled : Int :=
    if scaled < 0 then -(storedMagnitude : Int) else storedMagnitude
  (naturalScale, { unscaled, scale := storedScale })

end StoredNumber

end A12Kernel
