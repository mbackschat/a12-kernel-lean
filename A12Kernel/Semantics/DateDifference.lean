import A12Kernel.Semantics.BaseYearDateSource
import A12Kernel.Semantics.DateShift
import A12Kernel.Semantics.NumericComparison

/-! # Date-only month/year differences

This capsule computes the signed count of completed calendar months or years over decoded date parts, then exposes that mechanism through stored/full Dates, direct or range-selected Base-Year sources, and one phase-observed numeric operand boundary. It orders the operands, tests the direct candidate period against the later date using the matching shift convention, and restores the original sign.

The shared decoded-parts mechanism does not itself accept arbitrary authored dates. Its consumers retain their own boundaries: `FullDate` preserves the stored-value floor, while configured Base Year remains floor-free. The observed operand boundary preserves formal-cause precedence and symmetric empty-to-zero provenance while refusing legacy-hybrid values. Checked field/Base-Year lowering, static Date-only/component gates, scale 0, validation polarity, and computation poison are supplied by the shared numeric-expression consumers; constructed `Date(...)` legacy-hybrid execution, DateTime, and temporal targets remain outside.
-/

namespace A12Kernel

/-- The two date-only completed-period units whose result is a scale-0 Number. -/
inductive DateDifferenceUnit where
  | months
  | years
  deriving Repr, DecidableEq

namespace DateDifferenceUnit

/-- Static component admission after the separate ordinary-Date and partially-known checks. -/
def admittedBy (unit : DateDifferenceUnit) (hasBaseYear : Bool)
    (components : TemporalComponents) : Bool :=
  !components.hasTime && components.hasDate &&
    match unit with
    | .months => components.month
    | .years => components.year || hasBaseYear

/-- The checker permits unlike year presence only when the model supplies Base Year. -/
def compatible (unit : DateDifferenceUnit) (hasBaseYear : Bool)
    (left right : TemporalComponents) : Bool :=
  unit.admittedBy hasBaseYear left && unit.admittedBy hasBaseYear right &&
    (hasBaseYear || left.year == right.year)

end DateDifferenceUnit

namespace DateParts

namespace Difference

/-- Linear year/month coordinate used to obtain the only two possible forward month counts. -/
def monthCoordinate (parts : DateParts) : Int :=
  parts.year * 12 + Int.ofNat parts.month - 1

/-- An admitted consumer supplies a real month; zero is an unreachable defensive default. -/
def monthLastDay (parts : DateParts) : Nat :=
  (DateParts.daysInMonth? parts.year parts.month).getD 0

/-- Completed months for an already ordered pair. The raw coordinate count is reduced only when its clamped landing passes the later day. -/
def wholeMonthsForward (earlier later : DateParts) : Int :=
  let candidate := monthCoordinate later - monthCoordinate earlier
  let landingDay :=
    DateParts.Shift.monthLandingDay earlier (monthLastDay later)
  if later.day < landingDay then candidate - 1 else candidate

/-- Completed years for an already ordered pair. The candidate landing follows `AddYears`, including last-of-February preservation. -/
def wholeYearsForward (source target : DateParts) : Int :=
  let candidate := target.year - source.year
  if source.month < target.month then
    candidate
  else if target.month < source.month then
    candidate - 1
  else
    let landingDay :=
      DateParts.Shift.yearLandingDay source (monthLastDay source)
        (monthLastDay target)
    if target.day < landingDay then candidate - 1 else candidate

/-- Restore the original operand order after evaluating a nonnegative whole-period count. Equal operands reach the reverse branch and still produce zero. -/
def signedWholePeriods
    (forward : DateParts → DateParts → Int)
    (first second : DateParts) : Int :=
  if decide (first.Before second) then forward first second
  else -(forward second first)

end Difference

end DateParts

namespace DateDifferenceUnit

/-- Apply the selected completed-period core to two already-admitted decoded dates. -/
def between (unit : DateDifferenceUnit) (first second : DateParts) : Int :=
  match unit with
  | .months =>
      DateParts.Difference.signedWholePeriods
        DateParts.Difference.wholeMonthsForward first second
  | .years =>
      DateParts.Difference.signedWholePeriods
        DateParts.Difference.wholeYearsForward first second

end DateDifferenceUnit

/-- One runtime date-difference operand after phase observation. Legacy-hybrid values stay explicit because the decoded Gregorian core is not valid for their cutover cases. -/
inductive DateDifferenceOperand where
  | empty
  | value (parts : DateParts)
  | unavailable (cause : FormalCause)
  | unsupportedCalendar
  deriving Repr, DecidableEq

namespace DateDifferenceOperand

/-- Project one observed scalar Date. Static admission has already rejected DateTime. -/
def ofObservation : CellObservation Value → DateDifferenceOperand
  | .empty => .empty
  | .value (.temporal (.date _ parts .storedGregorian)) => .value parts
  | .value (.temporal (.date _ _ .legacyHybrid)) => .unsupportedCalendar
  | .value _ => .unavailable .malformed
  | .unknown cause | .poison cause => .unavailable cause

/-- Formal unavailability dominates emptiness; emptiness then yields the kernel's symmetric zero without inspecting the other present operand's calendar. -/
def evaluate (unit : DateDifferenceUnit)
    (left right : DateDifferenceOperand) : Except Unit NumericOperand :=
  match left, right with
  | .unavailable cause, _ => pure (.unknown cause)
  | _, .unavailable cause => pure (.unknown cause)
  | .empty, _ | _, .empty => pure (.value 0 .both)
  | .unsupportedCalendar, _ | _, .unsupportedCalendar => throw ()
  | .value first, .value second => pure (.value (unit.between first second) .fixed)

end DateDifferenceOperand

namespace FullDate

namespace Difference

/-- Stored-Date specialization of the shared decoded-parts month counter. -/
def wholeMonthsForward (earlier later : FullDate) : Int :=
  DateParts.Difference.wholeMonthsForward earlier.civil.parts later.civil.parts

/-- Stored-Date specialization of the shared decoded-parts year counter. -/
def wholeYearsForward (earlier later : FullDate) : Int :=
  DateParts.Difference.wholeYearsForward earlier.civil.parts later.civil.parts

/-- Restore stored-Date operand order while retaining the established `FullDate` proof seam. -/
def signedWholePeriods
    (forward : FullDate → FullDate → Int)
    (first second : FullDate) : Int :=
  if first.before second then forward first second
  else -(forward second first)

end Difference

/-- Signed count of complete month shifts from the first admitted Date to the second. -/
def differenceInMonths (first second : FullDate) : Int :=
  Difference.signedWholePeriods Difference.wholeMonthsForward first second

/-- Signed count of complete year shifts from the first admitted Date to the second. -/
def differenceInYears (first second : FullDate) : Int :=
  Difference.signedWholePeriods Difference.wholeYearsForward first second

end FullDate

/-- Signed count of complete month shifts between two direct or range-selected projections of the configured Base Year. -/
def baseYearDateDifferenceInMonths (year : Int)
    (first second : BaseYearDateSource) : Int :=
  DateParts.Difference.signedWholePeriods DateParts.Difference.wholeMonthsForward
    (first.parts year) (second.parts year)

/-- Signed count of complete year shifts between two direct or range-selected projections of the configured Base Year. -/
def baseYearDateDifferenceInYears (year : Int)
    (first second : BaseYearDateSource) : Int :=
  DateParts.Difference.signedWholePeriods DateParts.Difference.wholeYearsForward
    (first.parts year) (second.parts year)

end A12Kernel
