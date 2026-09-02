import A12Kernel.Core

/-! # Decoded numeric literals and host-integer conversion

This module owns numeric-token identity after decimal decoding and the measured Java `Double.parseDouble` → `Math.round` → signed-`int` conversion shared by static iteration legality and rule-set mandatory-information analysis. Runtime arithmetic and numeric comparison retain their existing owners. -/

namespace A12Kernel

/-- One numeric token after decoding. `authoredScale` is syntax metadata and cannot be recovered from `value`; for example, `0` and `0.00` have the same value but scales 0 and 2. -/
structure DecodedNumericLiteral where
  value : Rat
  authoredScale : Int
  deriving Repr, DecidableEq

namespace DecodedNumericLiteral

private def pow2Rat (exponent : Int) : Rat :=
  if 0 ≤ exponent then
    (2 ^ exponent.toNat : Nat)
  else
    1 / (2 ^ (-exponent).toNat : Nat)

private def roundNonnegativeTiesEven (value : Rat) : Nat :=
  let numerator := value.num.toNat
  let denominator := value.den
  let quotient := numerator / denominator
  let remainder := numerator % denominator
  if 2 * remainder < denominator then
    quotient
  else if denominator < 2 * remainder then
    quotient + 1
  else if quotient % 2 == 0 then
    quotient
  else
    quotient + 1

private def floorLog2Positive (value : Rat) : Int :=
  let estimate :=
    Int.ofNat value.num.toNat.log2 - Int.ofNat value.den.log2
  if value < pow2Rat estimate then estimate - 1 else estimate

/-- Round one nonzero finite rational to the nearest IEEE-754 binary64 value, with ties to an even significand. Callers bound the magnitude below `2^63`, so overflow and infinities cannot arise here. -/
private def roundToBinary64 (value : Rat) : Rat :=
  let negative := value < 0
  let magnitude := if negative then -value else value
  let exponent := floorLog2Positive magnitude
  let stepExponent :=
    if magnitude < pow2Rat (-1022) then -1074 else exponent - 52
  let step := pow2Rat stepExponent
  let units := roundNonnegativeTiesEven (magnitude / step)
  let rounded := (units : Rat) * step
  if negative then -rounded else rounded

private def javaRoundedLong (value : Rat) : Int :=
  let longLimit : Rat := 2 ^ 63
  if longLimit ≤ value then
    9223372036854775807
  else if value ≤ -longLimit then
    -9223372036854775808
  else
    let binary64 := if value == 0 then 0 else roundToBinary64 value
    let rounded := (binary64 + 1 / 2).floor
    if (9223372036854775807 : Int) < rounded then
      9223372036854775807
    else if rounded < (-9223372036854775808 : Int) then
      -9223372036854775808
    else
      rounded

private def narrowSignedInt32 (value : Int) : Int :=
  let residue := value.emod 4294967296
  if residue < 2147483648 then residue else residue - 4294967296

/-- Reproduce the measured host conversion for one checked finite-decimal literal. Exact rational value plus authored scale is sufficient because the grammar admits no exponent and preserves every fractional digit; values outside that checked decimal shape remain explicit insufficiency. -/
def javaRoundedInt32? (literal : DecodedNumericLiteral) : Option Int :=
  if literal.authoredScale < 0 then
    none
  else if (literal.value *
      (10 ^ literal.authoredScale.toNat : Nat)).den != 1 then
    none
  else
    some (narrowSignedInt32 (javaRoundedLong literal.value))

end DecodedNumericLiteral

end A12Kernel
