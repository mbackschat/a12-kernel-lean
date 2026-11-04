import A12Kernel.Semantics.BaseYearDateSource
import A12Kernel.Semantics.DateShift
import A12Kernel.Semantics.DateTimeDayDifference
import A12Kernel.Semantics.NumericComparison

/-! # Checked calendar differences

This capsule computes signed calendar differences through one phase-observed numeric operand boundary. Date-only month/year differences use decoded date parts; day differences preserve both the decoded proleptic Date/DateTime label and its already-resolved exact instant for a selected model-zone profile. A date constant enters a day difference through its stored-label resolution, which gives a Julian leap day its Julian instant under UTC and none under Europe/Berlin, and `Today` and a Base Year enter on the proleptic calendar (spec/05 §1, §2.7). Stored/full Dates, admitted date literals and direct or range-selected Base-Year sources share the boundary.

The shared decoded-parts mechanism does not itself accept arbitrary authored dates. Its consumers retain their own boundaries: `FullDate` preserves the stored-value floor, while configured Base Year remains floor-free. The observed operand boundary preserves formal-cause precedence and symmetric empty-to-zero provenance, and it fails the evaluation for a date constant the model zone gives no instant, a Julian leap day under Europe/Berlin (spec/05 §1). Checked field/literal/Base-Year lowering, per-operation kind/component gates, concrete profile selection, scale 0, validation polarity, and computation poison are supplied by the shared numeric-expression consumers; constructed `Date(...)` execution, wider authored temporal operands, and temporal targets remain outside.
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

/-- Why a completed-period difference refuses an operand pair. `compatible` above answers *whether*,
which was all this family had while its refusal classes were unmeasured; a12-dmkits measured them on
both units across a declared/absent Base-Year pair, so the three grounds now carry distinct Kernel
codes and a consumer mapping refusal to repair needs which one fired.

This deliberately does **not** reuse [`TemporalOperationUnit.OperandFault`](TemporalFormat.lean),
whose result domain is the two grounds its own family can report. The completed-period family has a
third, and the extra one is Base-Year-conditioned rather than an ordinary granularity refusal, so the
two are parallel accounts of different sizes rather than one shared mechanism. -/
inductive DifferenceOperandFault where
  /-- `MVK_WRONG_DATE_FORMAT_FOR_OP` — an operand lacks the component the unit steps. -/
  | granularity
  /-- `MVK_DATE_WITH_AND_WITHOUT_YEAR` — both operands step, and exactly one carries a year. -/
  | yearDisagreement
  /-- `MVK_INVALID_TIME` — a pure clock operand where a declared Base Year has already satisfied the
  year requirement, so the question that answers instead is whether any calendar component exists. -/
  | invalidTime
  deriving Repr, DecidableEq

/-- Whether a declared Base Year has satisfied this unit's own component requirement, leaving a pure
clock operand to be refused as a time rather than as a granularity. Only `years` takes its component
from the Base Year, which is why `months` reports the ordinary granularity code on the same operand. -/
private def clockOutlivesComponentGate (unit : DateDifferenceUnit) (hasBaseYear : Bool)
    (components : TemporalComponents) : Bool :=
  unit == .years && hasBaseYear && components.hasTime && !components.hasDate

/-- Classify one operand pair. The order is measured rather than chosen: a pure clock under a
declared Base Year reports the time code although it also fails granularity, and a year mixture is
only reachable once both operands step. `none` is admission and agrees with `compatible`. -/
def operandFault? (unit : DateDifferenceUnit) (hasBaseYear : Bool)
    (left right : TemporalComponents) : Option DifferenceOperandFault :=
  if unit.clockOutlivesComponentGate hasBaseYear left
      || unit.clockOutlivesComponentGate hasBaseYear right then
    some .invalidTime
  else if !(unit.admittedBy hasBaseYear left && unit.admittedBy hasBaseYear right) then
    some .granularity
  else if !(hasBaseYear || left.year == right.year) then
    some .yearDisagreement
  else none

end DateDifferenceUnit

namespace CalendarDayDifference

/-- Static day-difference admission requires a date-bearing format with a day component; a time half
    is permitted. The declared **kind** is deliberately absent: the Kernel reads the declared format
    here and never the kind, so a TIME- or DATE_TIME-declared field whose format is a complete date
    is admitted while a DATE-declared field whose format is a bare clock is refused
    ([checkpoint](../../docs/sources/computation-placement-and-constant-probes.md#src-temporal-difference-gates-read-the-format)).
    An earlier `admitsKind` conjunct here refused the first of those, which was a wrong refusal. -/
def admittedBy (components : TemporalComponents) : Bool :=
  components.hasDate && components.day

/-- Day differences share the date-difference year-presence gate after each operand's kind/component admission. -/
def yearCompatible (hasBaseYear : Bool)
    (left right : TemporalComponents) : Bool :=
  (hasBaseYear || left.year == right.year)

end CalendarDayDifference

namespace DateParts

namespace Difference

/-- An admitted consumer supplies a real month; zero is an unreachable defensive default. -/
def monthLastDay (parts : DateParts) : Nat :=
  (DateParts.daysInMonth? parts.year parts.month).getD 0

/-- Completed months for an already ordered pair. The raw coordinate count is reduced only when its clamped landing passes the later day. -/
def wholeMonthsForward (earlier later : DateParts) : Int :=
  let candidate := later.monthCoordinate - earlier.monthCoordinate
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

/-- One runtime date-difference operand after phase observation. -/
inductive DateDifferenceOperand where
  | empty
  | value (parts : DateParts)
  | unavailable (cause : FormalCause)
  /-- A date constant the model zone gives no instant, a Julian leap day under Europe/Berlin (spec/05 §1). Reaching it fails the evaluation, which is a value failure and no formal cause. -/
  | noInstantConstant
  deriving Repr, DecidableEq

/-- Why a difference evaluation fails instead of yielding a number. -/
inductive DifferenceEvaluationFault where
  /-- An operand constant has no instant in the model zone. -/
  | constantHasNoInstant
  /-- An operand has no label or instant in the selected calendar profile. -/
  | unsupportedCalendar
  deriving Repr, DecidableEq

namespace DateDifferenceOperand

/-- Project one observed scalar Date. Static admission has already rejected DateTime. -/
def ofObservation : CellObservation Value → DateDifferenceOperand
  | .empty => .empty
  | .value (.temporal (.date date)) => .value date.parts
  | .value _ => .unavailable .malformed
  | .unknown cause | .poison cause => .unavailable cause

/-- A date constant as a completed-period difference reads it when reached (spec/05 §1). A label real on the proleptic calendar is its own date. A Julian leap day the proleptic calendar lacks reads as the date of the label decoded at its Julian instant under UTC, and has no instant under Europe/Berlin. -/
def ofConstant (profile : ModelZone.ConcreteProfile) (parts : DateParts) : DateDifferenceOperand :=
  if parts.isJulianOnly then
    match (profile.resolveStoredLabel? (CalendarLabel.midnight parts)).bind profile.calendarLabel? with
    | some label => .value label.parts
    | none => .noInstantConstant
  else .value parts

/-- A constant without an instant fails the evaluation ahead of every other operand state, because the constant is reached whatever the other operand holds. Formal unavailability then dominates emptiness; emptiness yields the kernel's symmetric zero. The ordering of the failure against the other states is unmeasured on 31.1.1. -/
def evaluate (unit : DateDifferenceUnit)
    (left right : DateDifferenceOperand) : Except DifferenceEvaluationFault NumericOperand :=
  match left, right with
  | .noInstantConstant, _ | _, .noInstantConstant => throw .constantHasNoInstant
  | .unavailable cause, _ => pure (.unknown cause)
  | _, .unavailable cause => pure (.unknown cause)
  | .empty, _ | _, .empty => pure (.value 0 .both)
  | .value first, .value second => pure (.value (unit.between first second) .fixed)

end DateDifferenceOperand

/-- One checked Date/DateTime operand for model-zone calendar-day difference. Exact instant identity remains paired with its decoded proleptic label (spec/05 §2.5, §2.7). -/
inductive CalendarDayDifferenceOperand where
  | empty
  | value (label : CalendarLabel) (instant : Instant)
  | unavailable (cause : FormalCause)
  | unsupportedCalendar
  /-- A date constant the model zone gives no instant, a Julian leap day under Europe/Berlin (spec/05 §1). Reaching it fails the evaluation as a value failure, which `unsupportedCalendar`, the answer for an operand outside the selected profile, does not. -/
  | noInstantConstant
  deriving Repr, DecidableEq

namespace CalendarDayDifferenceOperand

/-- Project one observed Date or DateTime without re-resolving its exact instant. -/
def ofObservation : CellObservation Value → CalendarDayDifferenceOperand
  | .empty => .empty
  | .value (.temporal (.date date)) =>
      .value (CalendarLabel.midnight date.parts) date.instant
  | .value (.temporal (.dateTime instant parts time)) =>
      .value { parts, time } instant
  | .value _ => .unavailable .malformed
  | .unknown cause | .poison cause => .unavailable cause

/-- Resolve an admitted calendar endpoint at its proleptic midnight in its model-zone profile. -/
def ofParts (profile : ModelZone.ConcreteProfile)
    (parts : DateParts) : CalendarDayDifferenceOperand :=
  let label := CalendarLabel.midnight parts
  match profile.resolveCalendarLabel? label with
  | some instant => .value label instant
  | none => .unsupportedCalendar

/-- Resolve an authored date constant as a stored label resolves (spec/05 §1): under UTC a Julian leap day the proleptic calendar lacks keeps its Julian instant, and the label then decodes to the day that instant names. Under Europe/Berlin such a constant has no instant and the difference fails when reached. -/
def ofConstant (profile : ModelZone.ConcreteProfile)
    (parts : DateParts) : CalendarDayDifferenceOperand :=
  match profile.resolveStoredLabel? (CalendarLabel.midnight parts) with
  | some instant =>
      match profile.calendarLabel? instant with
      | some label => .value label instant
      | none => .unsupportedCalendar
  | none => if parts.isJulianOnly then .noInstantConstant else .unsupportedCalendar

/-- One exact instant at its local wall label in the model zone, as `Now` enters a day difference.
The instant keeps its millisecond remainder (spec/05 §7). -/
def ofInstant (profile : ModelZone.ConcreteProfile) (instant : Instant) : CalendarDayDifferenceOperand :=
  match profile.calendarLabel? instant with
  | some label => .value label instant
  | none => .unsupportedCalendar

/-- Resolve one direct or range-selected Base-Year endpoint through the common midnight boundary. -/
def ofBaseYear (profile : ModelZone.ConcreteProfile) (year : Int)
    (source : BaseYearDateSource) : CalendarDayDifferenceOperand :=
  ofParts profile (source.parts year)

/-- A constant without an instant fails the evaluation ahead of every other operand state, because the constant is reached whatever the other operand holds; the ordering is unmeasured on 31.1.1. Formal unavailability then dominates empty substitution. Empty then yields symmetric numeric zero; present values delegate to the selected exact-instant calendar-step profile. -/
def evaluate (profile : ModelZone.ConcreteProfile)
    (left right : CalendarDayDifferenceOperand) :
    Except DifferenceEvaluationFault NumericOperand :=
  match left, right with
  | .noInstantConstant, _ | _, .noInstantConstant => throw .constantHasNoInstant
  | .unavailable cause, _ => pure (.unknown cause)
  | _, .unavailable cause => pure (.unknown cause)
  | .empty, _ | _, .empty => pure (.value 0 .both)
  | .unsupportedCalendar, _ | _, .unsupportedCalendar => throw .unsupportedCalendar
  | .value _ firstInstant, .value _ secondInstant =>
      match profile.differenceResolvedInDays? firstInstant secondInstant with
      | some days => pure (.value days .fixed)
      | none => throw .unsupportedCalendar

end CalendarDayDifferenceOperand

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
