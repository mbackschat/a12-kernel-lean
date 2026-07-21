import A12Kernel.Semantics.DateTime

/-! # A12Kernel.Semantics.DateTimeDifference — resolved sub-day instant differences

This capsule implements the post-resolution core of [`spec/05-dates-and-time.md` §2](../../spec/05-dates-and-time.md#2-addition-and-difference-are-asymmetric-and-calendar-corrected). Both operands are already exact instants. It computes `second − first` in authored argument order and divides by the selected positive unit with truncation toward zero.

Parsing, zone resolution, empty and malformed operands, static operator admission, numeric result storage, validation polarity, and the Date/DateTime `DifferenceInDays` wall-coordinate rule remain separate.
-/

namespace A12Kernel

/-- The three sub-day DateTime-difference units. Closing the enum makes a zero divisor unrepresentable. -/
inductive DateTimeDifferenceUnit where
  | hours
  | minutes
  | seconds
  deriving Repr, DecidableEq

namespace DateTimeDifferenceUnit

/-- Positive whole seconds in one admitted unit. -/
def unitSeconds : DateTimeDifferenceUnit → Int
  | .hours => 3600
  | .minutes => 60
  | .seconds => 1

end DateTimeDifferenceUnit

namespace Instant

/-- Return the exact epoch-millisecond delta divided by the selected unit, using `Int.tdiv` so negative fractional results truncate toward zero. -/
def difference (first : Instant) (unit : DateTimeDifferenceUnit)
    (second : Instant) : Int :=
  (second.epochMillis - first.epochMillis).tdiv (unit.unitSeconds * 1000)

end Instant

end A12Kernel
