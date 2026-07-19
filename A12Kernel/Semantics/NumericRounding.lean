import A12Kernel.Core

/-! # A12Kernel.Semantics.NumericRounding — two-stage decimal rounding -/

namespace A12Kernel

/-- The kernel first rounds to this decimal scale before applying an authored rounding mode. -/
def decimalPreRoundScale : Nat := 19

/-- Greatest authored count of fractional digits accepted by a rounding operation. -/
def maxRoundingPlaces : Nat := 14

/-- A statically accepted authored rounding scale: exactly `0..14`. -/
abbrev RoundingPlaces := Fin (maxRoundingPlaces + 1)

namespace RoundingPlaces

/-- Admit an authored natural exactly when it lies in the kernel's `0..14` range. -/
def ofNat? (places : Nat) : Option RoundingPlaces :=
  if valid : places < maxRoundingPlaces + 1 then
    some ⟨places, valid⟩
  else
    none

/- The rounding result's static scale is the requested number of places. -/
def resultScale (places : RoundingPlaces) : ScaleInfo :=
  .exact places.val

end RoundingPlaces

/-- Omitting the authored decimal-places argument is exactly the zero-places form. -/
def omittedRoundingPlaces : RoundingPlaces := ⟨0, by decide⟩

/-- Mathematical target-scale modes underlying the three A12 rounding families. -/
inductive DecimalRoundingMode where
  | floor
  | ceiling
  | halfUp
  deriving Repr, DecidableEq

/-- Exact power-of-ten factor for a fixed decimal scale. -/
def decimalFactor (scale : Nat) : Nat :=
  10 ^ scale

/-- Decimal `HALF_UP`, i.e. exact ties round away from zero. -/
def rescaleHalfUp (value : Rat) (scale : Nat) : Rat :=
  let factor := decimalFactor scale
  let shifted := value * (factor : Rat)
  let half : Rat := 1 / 2
  let rounded := if shifted < 0 then Rat.ceil (shifted - half) else Rat.floor (shifted + half)
  (rounded : Rat) / (factor : Rat)

/-- Rescale toward negative infinity. -/
def rescaleFloor (value : Rat) (scale : Nat) : Rat :=
  let factor := decimalFactor scale
  (Rat.floor (value * (factor : Rat)) : Rat) / (factor : Rat)

/-- Rescale toward positive infinity. -/
def rescaleCeiling (value : Rat) (scale : Nat) : Rat :=
  let factor := decimalFactor scale
  (Rat.ceil (value * (factor : Rat)) : Rat) / (factor : Rat)

/-- Apply the kernel's scale-19 `HALF_UP` pre-round and then the authored target-scale mode. -/
def roundDecimal (mode : DecimalRoundingMode) (value : Rat) (places : RoundingPlaces) : Rat :=
  let preRounded := rescaleHalfUp value decimalPreRoundScale
  match mode with
  | .floor => rescaleFloor preRounded places.val
  | .ceiling => rescaleCeiling preRounded places.val
  | .halfUp => rescaleHalfUp preRounded places.val

end A12Kernel
