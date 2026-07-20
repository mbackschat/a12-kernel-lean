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

/-- Return `(second − first) / unit` with `Int.tdiv`, which truncates negative fractional results toward zero. -/
def difference (first : Instant) (unit : DateTimeDifferenceUnit)
    (second : Instant) : Int :=
  (second.epochSecond - first.epochSecond).tdiv unit.unitSeconds

end Instant

end A12Kernel
