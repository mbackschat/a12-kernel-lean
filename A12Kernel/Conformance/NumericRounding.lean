import A12Kernel.Semantics.NumericComparison

/-! # Decimal-rounding separating cases -/

namespace A12Kernel.Conformance.NumericRounding

open A12Kernel

private def zeroPlaces : RoundingPlaces := ⟨0, by decide⟩
private def onePlace : RoundingPlaces := ⟨1, by decide⟩
private def fourteenPlaces : RoundingPlaces := ⟨14, by decide⟩

example : RoundingPlaces.ofNat? 0 = some zeroPlaces := by
  decide

example : RoundingPlaces.ofNat? 14 = some fourteenPlaces := by
  decide

example : RoundingPlaces.ofNat? 15 = none := by
  decide

example : omittedRoundingPlaces = zeroPlaces := by
  rfl

example : zeroPlaces.resultScale = .exact 0 := by
  rfl

example : fourteenPlaces.resultScale = .exact 14 := by
  rfl

/- A12 `RoundDown` is mathematical floor, including for negative values. -/
example : roundDecimal .floor ((-14 : Rat) / 10) zeroPlaces = -2 := by
  native_decide

example : roundDecimal .floor ((18 : Rat) / 10) zeroPlaces = 1 := by
  native_decide

/- A12 `RoundUp` is mathematical ceiling, not away-from-zero rounding. -/
example : roundDecimal .ceiling ((-14 : Rat) / 10) zeroPlaces = -1 := by
  native_decide

example : roundDecimal .ceiling ((12 : Rat) / 10) zeroPlaces = 2 := by
  native_decide

example : roundDecimal .halfUp ((25 : Rat) / 10) zeroPlaces = 3 := by
  native_decide

example : roundDecimal .halfUp ((-25 : Rat) / 10) zeroPlaces = -3 := by
  native_decide

example : roundDecimal .halfUp ((465 : Rat) / 100) onePlace = 47 / 10 := by
  native_decide

private def almostOne : Rat := 1 - 1 / (10 ^ 50)

/- The scale-19 pre-round occurs before the requested floor. -/
example : roundDecimal .floor almostOne zeroPlaces = 1 := by
  native_decide

/- Without that pre-round, flooring the same exact rational would produce zero. -/
example : (Rat.floor almostOne : Rat) = 0 := by
  native_decide

/- Consequently, the usual floor bound does not hold against the raw pre-normalized input. -/
example : roundDecimal .floor almostOne zeroPlaces > almostOne := by
  native_decide

private def justAboveOne : Rat := 1 + 1 / (10 ^ 50)

/- The dual raw-input ceiling bound is also false after the pre-round. -/
example : roundDecimal .ceiling justAboveOne zeroPlaces = 1 := by
  native_decide

example : (Rat.ceil justAboveOne : Rat) = 2 := by
  native_decide

example : roundDecimal .ceiling justAboveOne zeroPlaces < justAboveOne := by
  native_decide

example : (NumericOperand.unknown .malformed).round .floor zeroPlaces =
    .unknown .malformed := by
  rfl

example : (NumericOperand.value almostOne (.emptyNumber true)).round .floor zeroPlaces =
    .value 1 (.emptyNumber true) := by
  native_decide

end A12Kernel.Conformance.NumericRounding
