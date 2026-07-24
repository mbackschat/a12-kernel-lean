import A12Kernel.Semantics.DateTime
import A12Kernel.Semantics.NumericComparison

/-! # A12Kernel.Semantics.DateTimeDifference — resolved sub-day instant differences

This capsule implements the post-resolution core of [`spec/05-dates-and-time.md` §2](../../spec/05-dates-and-time.md#2-addition-and-difference-are-asymmetric-and-calendar-corrected). Both operands are already exact instants. It computes `second − first` in authored argument order and divides by the selected positive unit with truncation toward zero.

Parsing, zone resolution, empty and malformed operands, static operator admission, numeric result storage, validation polarity, and the Date/DateTime `DifferenceInDays` model-zone calendar-step rule remain separate.
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

/-- Static DateTime-format admission requires a date half and the selected time component. Kind admission remains with the checked field owner. -/
def admittedBy (unit : DateTimeDifferenceUnit)
    (components : TemporalComponents) : Bool :=
  components.hasDate &&
    match unit with
    | .hours => components.hour
    | .minutes => components.minute
    | .seconds => components.second

/-- Both DateTime formats must support the selected unit and agree on explicit year presence. `BaseYear` is not a legal sub-day operand. -/
def compatible (unit : DateTimeDifferenceUnit)
    (left right : TemporalComponents) : Bool :=
  unit.admittedBy left && unit.admittedBy right &&
    left.year == right.year

end DateTimeDifferenceUnit

namespace Instant

/-- Return the exact epoch-millisecond delta divided by the selected unit, using `Int.tdiv` so negative fractional results truncate toward zero. -/
def difference (first : Instant) (unit : DateTimeDifferenceUnit)
    (second : Instant) : Int :=
  (second.epochMillis - first.epochMillis).tdiv (unit.unitSeconds * 1000)

end Instant

/-- One runtime sub-day difference operand after phase observation. Static checking has already restricted this boundary to DateTime fields. -/
inductive DateTimeDifferenceOperand where
  | empty
  | value (instant : Instant)
  | unavailable (cause : FormalCause)
  deriving Repr, DecidableEq

namespace DateTimeDifferenceOperand

/-- Project only an exact DateTime instant; a forged Date, Time, or non-temporal payload remains a formal kind failure. -/
def ofObservation : CellObservation Value → DateTimeDifferenceOperand
  | .empty => .empty
  | .value (.temporal (.dateTime instant _ _ _)) => .value instant
  | .value _ => .unavailable .malformed
  | .unknown cause | .poison cause => .unavailable cause

/-- Formal unavailability dominates empty substitution. Either missing operand then yields symmetric zero; two present values reuse the exact millisecond difference core. -/
def evaluate (unit : DateTimeDifferenceUnit)
    (left right : DateTimeDifferenceOperand) : NumericOperand :=
  match left, right with
  | .unavailable cause, _ => .unknown cause
  | _, .unavailable cause => .unknown cause
  | .empty, _ | _, .empty => .value 0 .both
  | .value first, .value second =>
      .value (first.difference unit second) .fixed

end DateTimeDifferenceOperand

end A12Kernel
