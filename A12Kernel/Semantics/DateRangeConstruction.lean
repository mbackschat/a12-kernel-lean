import A12Kernel.Semantics.DateRangeComparison
import A12Kernel.Semantics.TemporalTarget
import A12Kernel.Semantics.PartialDate

namespace A12Kernel

inductive DateRangeEndpointFormat where
  | full (format : FullDateTargetFormat)
  | yearFragment
  | yearMonthFragment
  | monthFragment (baseYear : Int)
  | monthDayFragment (baseYear : Int)
  | yearlessMonth
  | yearlessMonthDay
  deriving Repr, DecidableEq

namespace DateRangeEndpointFormat

/-- Recognize the checked endpoint profile; Base Year selects exact completion or retained yearless identity for `MM` and `MM-dd`.

A DateFragment endpoint is a component-omitting Date at full precision, named by its format, as the
reader decodes a `DateFragmentType`. A partial precision is a partially known full-format Date and no
endpoint here. -/
def ofPolicy? (baseYear : Option Int) (policy : TemporalTargetPolicy) :
    Option DateRangeEndpointFormat :=
  if policy.partialMode != .full then none
  else match FullDateTargetFormat.ofSource? policy.format with
    | some format => some (.full format)
    | none =>
        if policy.format == "yyyy" then
          some .yearFragment
        else if policy.format == "yyyy-MM" then
          some .yearMonthFragment
        else if policy.format == "MM" then
          match baseYear with
          | some year => some (.monthFragment year)
          | none => some .yearlessMonth
        else if policy.format == "MM-dd" then
          match baseYear with
          | some year => some (.monthDayFragment year)
          | none => some .yearlessMonthDay
        else
          none

/-- Exact component-set compatibility for the bounded endpoint profiles. Lexical spelling does not distinguish the two complete full-Date formats. -/
def sameComponents : DateRangeEndpointFormat → DateRangeEndpointFormat → Bool
  | .full _, .full _ => true
  | .yearFragment, .yearFragment => true
  | .yearMonthFragment, .yearMonthFragment => true
  | .monthFragment _, .monthFragment _ => true
  | .monthDayFragment _, .monthDayFragment _ => true
  | .yearlessMonth, .yearlessMonth => true
  | .yearlessMonthDay, .yearlessMonthDay => true
  | _, _ => false

/-- The date components one checked construction endpoint exposes. Base-Year completion does not
add the year here: a completed `MM` endpoint still answers for the month it declared, exactly as
a stored declaration does, so one component projection serves both sides of the match. -/
def components : DateRangeEndpointFormat → TemporalComponents
  | .full _ => TemporalComponents.fullDate
  | .yearFragment =>
      { TemporalComponents.fullDate with month := false, day := false }
  | .yearMonthFragment => { TemporalComponents.fullDate with day := false }
  | .monthFragment _ | .yearlessMonth =>
      { TemporalComponents.fullDate with year := false, day := false }
  | .monthDayFragment _ | .yearlessMonthDay =>
      { TemporalComponents.fullDate with year := false }

/-- Complete one decoded endpoint label by its authored range position. -/
def complete? (format : DateRangeEndpointFormat) (bound : DateRangeBound)
    (parts : DateParts) : Option FullDate :=
  match format, bound with
  | .full _, _ => FullDate.ofYmd? parts.year parts.month parts.day
  | .yearFragment, .start => (OmittedMonthDate.ofYear? parts.year).map (·.first)
  | .yearFragment, .finish => (OmittedMonthDate.ofYear? parts.year).map (·.last)
  | .yearMonthFragment, .start =>
      (OmittedDayDate.ofYearMonth? parts.year parts.month).map (·.first)
  | .yearMonthFragment, .finish =>
      (OmittedDayDate.ofYearMonth? parts.year parts.month).map (·.last)
  | .monthFragment year, .start =>
      (OmittedDayDate.ofYearMonth? year parts.month).map (·.first)
  | .monthFragment year, .finish =>
      (OmittedDayDate.ofYearMonth? year parts.month).map (·.last)
  | .monthDayFragment year, _ => FullDate.ofYmd? year parts.month parts.day
  | .yearlessMonth, _ | .yearlessMonthDay, _ => none

end DateRangeEndpointFormat

/-- One exact or yearless endpoint identity retained without fabricating unavailable components. -/
inductive DateRangeConstructionEndpointValue where
  | exact (value : DateValue)
  | month (value : Nat)
  | monthDay (value : MonthDayValue)
  deriving Repr, DecidableEq

/-- Both typed endpoint observations retained for Execute and Explain. -/
structure DateRangeConstructionObservation where
  start : CellObservation DateRangeConstructionEndpointValue
  finish : CellObservation DateRangeConstructionEndpointValue
  deriving Repr, DecidableEq

namespace DateRangeConstructionObservation

/-- Classify one construction for comparison. Formal unavailability dominates emptiness; two present endpoints must expose one common profile. Defensive mixed carriers fail closed as malformed. -/
def comparisonOperand (observation : DateRangeConstructionObservation) :
    SimpleComparisonOperand DateRangeCellValue :=
  match observation.start, observation.finish with
  | .unknown cause, _ | .poison cause, _ => .unknown cause
  | _, .unknown cause | _, .poison cause => .unknown cause
  | .empty, _ | _, .empty => .notEvaluated
  | .value (.exact start), .value (.exact finish) =>
      .value (.exact { start, finish }) true
  | .value (.month start), .value (.month finish) =>
      .value (.yearlessMonth start finish) true
  | .value (.monthDay start), .value (.monthDay finish) =>
      .value (.yearlessMonthDay start finish) true
  | .value _, .value _ => .unknown .malformed

end DateRangeConstructionObservation

namespace DateRangeEndpointFormat

/-- Complete one already-observed Date endpoint while preserving empty and formal states. Direct and semantic-index consumers share this sole positional completion boundary. -/
def evaluateObservationWith (format : DateRangeEndpointFormat)
    (profile : ModelZone.ConcreteProfile) (field : FieldId)
    (valueKind : FieldId → Error) (dateUnavailable : FieldId → DateValue → Error)
    (bound : DateRangeBound) (observation : CellObservation) :
    Except Error
      (CellObservation DateRangeConstructionEndpointValue) := do
  match observation with
  | .empty => pure .empty
  | .value (.temporal (.date value)) =>
      match format with
      | .yearlessMonth =>
          match DateParts.daysInMonth? 2000 value.parts.month with
          | some _ => pure (.value (.month value.parts.month))
          | none => throw (dateUnavailable field value)
      | .yearlessMonthDay =>
          match FullDate.ofYmd? 2000 value.parts.month value.parts.day with
          | some _ => pure (.value (.monthDay {
              month := value.parts.month
              day := value.parts.day }))
          | none => throw (dateUnavailable field value)
      | format =>
          match format.complete? bound value.parts with
          | none => throw (dateUnavailable field value)
          | some date =>
              let instant? := (LocalDateTime.ofDateHms? date 0 0 0).bind
                profile.resolveLocal?
              match instant? with
              | some instant => pure (.value (.exact {
                  instant
                  parts := date.civil.parts
                  basis := .storedGregorian }))
              | none => throw (dateUnavailable field value)
  | .value _ => throw (valueKind field)
  | .unknown cause => pure (.unknown cause)
  | .poison cause => pure (.poison cause)

end DateRangeEndpointFormat

end A12Kernel
