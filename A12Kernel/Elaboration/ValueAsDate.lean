import A12Kernel.Elaboration.TemporalTargetPolicy
import A12Kernel.Elaboration.TemporalShiftAmount
import A12Kernel.Semantics.DateComparison
import A12Kernel.Semantics.DateDifference
import A12Kernel.Semantics.DateShift
import A12Kernel.Semantics.NumericComputationResult
import A12Kernel.Semantics.Observation
import A12Kernel.Semantics.TimeConstruction

/-! # Checked partial-Date `ValueAsDate`

This capsule retains every admitted stored Date omission and resolves a known-year interval only after `FirstDay` or `LastDay` is selected. Direct comparison delegates the resulting full Date to the existing evaluator. Day/month/year shifting converts the reached numeric amount with Java `BigDecimal.intValue` semantics and retains a real civil landing below the universal Date floor for the later target check. Month/year difference delegates completed-period counting to the existing Date-difference core while retaining authored operand order. A shared checked zoned source supplies both bounded DateTime construction and the separate calendar-day-difference composition without allowing either consumer to replace the model-owned profile. DateTime construction combines the endpoint with one direct typed Time observation and distinguishes missing input from a present but unresolvable wall label. An unknown year remains cause-free non-relevance rather than acquiring a fabricated year. The bounded raw adapter accepts the two exact declaration formats already owned by temporal targets. Wider format syntax, detailed formal-error codes, wider Time expressions, target effects, and repeatable addressing remain separate.
-/

namespace A12Kernel

/-- Which boundary of a partially known Date the authored operation selects. -/
inductive ValueAsDateEndpoint where
  | firstDay
  | lastDay
  deriving Repr, DecidableEq

/-- The two full-Date boundaries denoted by one admitted literal omitted-day value. The private constructor prevents callers from pairing unrelated dates. -/
structure OmittedDayDate where
  private mk ::
  first : FullDate
  last : FullDate
  deriving Repr, DecidableEq

namespace OmittedDayDate

/-- Construct an omitted day only when both endpoint completions are real and satisfy the universal Date floor. Checking the first endpoint before execution preserves the kernel's completion-before-floor order. -/
def ofYearMonth? (year : Int) (month : Nat) : Option OmittedDayDate := do
  let first ← FullDate.ofYmd? year month 1
  let lastDay ← DateParts.daysInMonth? year month
  let last ← FullDate.ofYmd? year month lastDay
  pure { first, last }

/-- Select the authored interval boundary. -/
def resolve (date : OmittedDayDate) : ValueAsDateEndpoint → FullDate
  | .firstDay => date.first
  | .lastDay => date.last

end OmittedDayDate

/-- The two full-Date boundaries denoted by one admitted literal omitted-month value. The private constructor prevents callers from pairing unrelated years. -/
structure OmittedMonthDate where
  private mk ::
  first : FullDate
  last : FullDate
  deriving Repr, DecidableEq

namespace OmittedMonthDate

/-- Construct an omitted month only when the formal checker’s earliest completion and the corresponding latest completion are admitted Dates. -/
def ofYear? (year : Int) : Option OmittedMonthDate := do
  let first ← FullDate.ofYmd? year 1 1
  let last ← FullDate.ofYmd? year 12 31
  pure { first, last }

/-- Select the authored complete-year boundary. -/
def resolve (date : OmittedMonthDate) : ValueAsDateEndpoint → FullDate
  | .firstDay => date.first
  | .lastDay => date.last

end OmittedMonthDate

/-- One structurally legal stored shape before the declaration’s partial-precision policy is applied. An omitted year carries no synthetic replacement because the runtime suppresses it before interval completion. -/
inductive PartiallyKnownDateValue where
  | full (date : FullDate)
  | omittedDay (date : OmittedDayDate)
  | omittedMonth (date : OmittedMonthDate)
  | omittedYear
  deriving Repr, DecidableEq

namespace TemporalPartialMode

/-- Whether one legal stored shape is admitted by this declaration precision. Unknown components form a suffix: month omission entails day omission, and year omission entails both. -/
def admitsPartiallyKnownValue :
    TemporalPartialMode → PartiallyKnownDateValue → Bool
  | .full, _ => false
  | .dayOptional, .full _ | .dayOptional, .omittedDay _ => true
  | .dayOptional, .omittedMonth _ | .dayOptional, .omittedYear => false
  | .monthOptional, .full _
  | .monthOptional, .omittedDay _
  | .monthOptional, .omittedMonth _ => true
  | .monthOptional, .omittedYear => false
  | .yearOptional, _ => true

end TemporalPartialMode

/-- A stored partial-Date value certified against its exact declaration precision. -/
structure AdmittedPartiallyKnownDate (mode : TemporalPartialMode) where
  value : PartiallyKnownDateValue
  admitted : mode.admitsPartiallyKnownValue value = true
  deriving Repr, DecidableEq

/-- The operation-level result keeps unknown-year non-relevance distinct from a resolved Date. -/
inductive ValueAsDateResolution where
  | date (value : FullDate)
  | nonRelevant
  deriving Repr, DecidableEq

/-- One phase read after endpoint completion. Non-relevance is not a formal cause and therefore must not be forged into `CellObservation.unknown` or collapsed into ordinary emptiness. -/
inductive ValueAsDateObservation where
  | empty
  | date (value : FullDate)
  | nonRelevant
  | unavailable (cause : FormalCause)
  deriving Repr, DecidableEq

namespace PartiallyKnownDateValue

/-- Resolve only known-year intervals. The unknown-year case follows the runtime’s early non-relevance branch. -/
def resolve : PartiallyKnownDateValue → ValueAsDateEndpoint → ValueAsDateResolution
  | .full date, _ => .date date
  | .omittedDay date, endpoint => .date (date.resolve endpoint)
  | .omittedMonth date, endpoint => .date (date.resolve endpoint)
  | .omittedYear, _ => .nonRelevant

end PartiallyKnownDateValue

namespace AdmittedPartiallyKnownDate

private def ofValue? (mode : TemporalPartialMode)
    (value : PartiallyKnownDateValue) :
    Option (AdmittedPartiallyKnownDate mode) :=
  if h : mode.admitsPartiallyKnownValue value = true then
    some { value, admitted := h }
  else
    none

/-- Admit a fully known value under any partial precision. -/
def ofFull? (mode : TemporalPartialMode) (date : FullDate) :
    Option (AdmittedPartiallyKnownDate mode) :=
  ofValue? mode (.full date)

/-- Admit a literal omitted day only under a precision that permits it. -/
def ofOmittedDay? (mode : TemporalPartialMode)
    (year : Int) (month : Nat) : Option (AdmittedPartiallyKnownDate mode) := do
  let date ← OmittedDayDate.ofYearMonth? year month
  ofValue? mode (.omittedDay date)

/-- Admit a literal omitted month-and-day only under `MONTH_OPTIONAL` or `YEAR_OPTIONAL`. -/
def ofOmittedMonth? (mode : TemporalPartialMode)
    (year : Int) : Option (AdmittedPartiallyKnownDate mode) := do
  let date ← OmittedMonthDate.ofYear? year
  ofValue? mode (.omittedMonth date)

/-- Admit the all-zero unknown-year shape only under `YEAR_OPTIONAL`. -/
def unknownYear? (mode : TemporalPartialMode) :
    Option (AdmittedPartiallyKnownDate mode) :=
  ofValue? mode .omittedYear

/-- Resolve the certified stored shape after selecting the authored endpoint. -/
def resolve (date : AdmittedPartiallyKnownDate mode)
    (endpoint : ValueAsDateEndpoint) : ValueAsDateResolution :=
  date.value.resolve endpoint

end AdmittedPartiallyKnownDate

namespace CellObservation

/-- Resolve a present partial value while retaining unknown-year non-relevance outside the formal-cause domain. Validation and computation consumers choose their own projection of that cause-free state. -/
def resolvePartiallyKnownDate
    (observation : CellObservation (AdmittedPartiallyKnownDate mode))
    (endpoint : ValueAsDateEndpoint) : ValueAsDateObservation :=
  match observation with
  | .empty => .empty
  | .value date =>
      match date.resolve endpoint with
      | .date resolved => .date resolved
      | .nonRelevant => .nonRelevant
  | .unknown cause | .poison cause => .unavailable cause

end CellObservation

/-- Static refusal before the bounded partial-Date direct-comparison consumer can execute. -/
inductive ValueAsDateElabError where
  | sourcePolicy (error : TemporalTargetElabError)
  | sourceKind (source : FieldId) (actual : TemporalKind)
  | unsupportedPartialMode (source : FieldId) (actual : TemporalPartialMode)
  | unsupportedFormat (source : FieldId) (format : String)
  deriving Repr, DecidableEq

/-- One checked partial-Date source whose declaration policy, interval endpoint, and raw format cannot be replaced independently after elaboration. Comparison and calendar shifting share this exact admission boundary. -/
structure CheckedValueAsDateSource (model : FlatModel) where
  source : CheckedTemporalTargetPolicy model
  endpoint : ValueAsDateEndpoint
  format : FullDateTargetFormat
  sourceIsDate : source.target.kind = .date
  sourceIsPartial : source.policy.partialMode ≠ .full
  formatMatches :
    FullDateTargetFormat.ofSource? source.policy.format = some format

namespace CheckedValueAsDateSource

/-- Decode one exact-width ASCII component. The bounded parser deliberately accepts no locale digits or width relaxation. -/
private def parseComponent? (width : Nat) (text : String) : Option Nat :=
  if text.length = width then parseAsciiNatural? text else none

/-- Decode the three stored components in semantic year/month/day order for the checked exact format. -/
private def parseStoredParts?
    (format : FullDateTargetFormat) (text : String) :
    Option (Nat × Nat × Nat) :=
  match format, text.splitOn (match format with
    | .dayMonthYearDots => "."
    | .yearMonthDayDashes => "-") with
  | .dayMonthYearDots, [dayText, monthText, yearText] => do
      let day ← parseComponent? 2 dayText
      let month ← parseComponent? 2 monthText
      let year ← parseComponent? 4 yearText
      pure (year, month, day)
  | .yearMonthDayDashes, [yearText, monthText, dayText] => do
      let year ← parseComponent? 4 yearText
      let month ← parseComponent? 2 monthText
      let day ← parseComponent? 2 dayText
      pure (year, month, day)
  | _, _ => none

private def admitKnownYearParts?
    (mode : TemporalPartialMode) (year month day : Nat) :
    Option (AdmittedPartiallyKnownDate mode) :=
  if month = 0 then
    if day = 0 then
      AdmittedPartiallyKnownDate.ofOmittedMonth? mode year
    else
      none
  else if day = 0 then
    AdmittedPartiallyKnownDate.ofOmittedDay? mode year month
  else
    (FullDate.ofYmd? year month day).bind
      (AdmittedPartiallyKnownDate.ofFull? mode)

/-- Apply suffix legality, calendar/floor admission, and the declaration’s optional pre-1900 check after exact lexical decoding. Unknown year is the sole exception to the pre-1900 branch because formal validation substitutes 2000 and runtime evaluation later marks it non-relevant. -/
private def admitStoredParts?
    (mode : TemporalPartialMode) (youngerThan1900Check : Bool)
    (year month day : Nat) :
    Option (AdmittedPartiallyKnownDate mode) :=
  if year = 0 then
    if month = 0 then
      if day = 0 then AdmittedPartiallyKnownDate.unknownYear? mode else none
    else
      none
  else if youngerThan1900Check then
    if year < 1900 then none else admitKnownYearParts? mode year month day
  else
    admitKnownYearParts? mode year month day

/-- Project raw stored text through the checked declaration policy. All lexical, suffix, calendar, floor, and enabled pre-1900 failures become the ordinary malformed formal finding before the operation reads the cell. -/
def checkSourceRaw (checked : CheckedValueAsDateSource model)
    (raw : RawCell String) :
    CheckedCell (AdmittedPartiallyKnownDate checked.source.policy.partialMode) :=
  checkRawCellWith (fun text =>
    match parseStoredParts? checked.format text with
    | none => .error .malformed
    | some (year, month, day) =>
        match admitStoredParts? checked.source.policy.partialMode
            checked.source.policy.youngerThan1900Check year month day with
        | none => .error .malformed
        | some value => .ok (some value)) raw

/-- Resolve one parser-admitted checked cell at the selected interval endpoint for an operation-specific consumer. -/
def observe (checked : CheckedValueAsDateSource model)
    (phase : Phase)
    (cell : CheckedCell
      (AdmittedPartiallyKnownDate checked.source.policy.partialMode)) :
    ValueAsDateObservation :=
  (observeCell phase cell).resolvePartiallyKnownDate checked.endpoint

end CheckedValueAsDateSource

/-- Resolve and certify one nonrepeatable partial-Date source for every partial precision. -/
def elaborateValueAsDateSource
    (model : FlatModel) (sourceField : FieldId)
    (endpoint : ValueAsDateEndpoint) :
    Except ValueAsDateElabError (CheckedValueAsDateSource model) := do
  let source ←
    elaborateTemporalTargetPolicy model sourceField |>.mapError .sourcePolicy
  if hKind : source.target.kind = .date then
    if hMode : source.policy.partialMode ≠ .full then
      match hFormat :
          FullDateTargetFormat.ofSource? source.policy.format with
      | none => throw (.unsupportedFormat sourceField source.policy.format)
      | some format =>
          pure {
            source
            endpoint
            format
            sourceIsDate := hKind
            sourceIsPartial := hMode
            formatMatches := hFormat }
    else
      throw (.unsupportedPartialMode sourceField source.policy.partialMode)
  else
    throw (.sourceKind sourceField source.target.kind)

/-- One checked direct comparison that specializes the shared partial-Date source admission. -/
structure CheckedValueAsDateComparison (model : FlatModel)
    extends CheckedValueAsDateSource model where
  comparison : TemporalComparisonOp
  expected : FullDate

namespace CheckedValueAsDateComparison

/-- Shared raw-source projection retained at the comparison boundary for existing direct consumers. -/
def checkSourceRaw (checked : CheckedValueAsDateComparison model)
    (raw : RawCell String) :
    CheckedCell (AdmittedPartiallyKnownDate checked.source.policy.partialMode) :=
  checked.toCheckedValueAsDateSource.checkSourceRaw raw

/-- Shared endpoint observation retained at the comparison boundary for its direct laws. -/
def observe (checked : CheckedValueAsDateComparison model)
    (phase : Phase)
    (cell : CheckedCell
      (AdmittedPartiallyKnownDate checked.source.policy.partialMode)) :
    ValueAsDateObservation :=
  checked.toCheckedValueAsDateSource.observe phase cell

/-- Evaluate one already parser-admitted stored value through the existing checked-cell observation and full-Date comparison paths. -/
def evaluate (checked : CheckedValueAsDateComparison model)
    (cell : CheckedCell
      (AdmittedPartiallyKnownDate checked.source.policy.partialMode)) : Verdict :=
  match checked.observe Phase.validation cell with
  | .empty => .notFired
  | .nonRelevant | .unavailable _ => .unknown
  | .date resolved =>
      checked.comparison.eval
        (.value resolved true) (.value checked.expected true)

/-- Check and evaluate one exact stored-text input without exposing an unchecked partial-Date constructor. -/
def evaluateRaw (checked : CheckedValueAsDateComparison model)
    (raw : RawCell String) : Verdict :=
  checked.evaluate (checked.checkSourceRaw raw)

end CheckedValueAsDateComparison

/-- Resolve and certify the nonrepeatable direct-comparison `ValueAsDate` slice for every partial precision. -/
def elaborateValueAsDateComparison
    (model : FlatModel) (sourceField : FieldId)
    (endpoint : ValueAsDateEndpoint)
    (comparison : TemporalComparisonOp) (expected : FullDate) :
    Except ValueAsDateElabError (CheckedValueAsDateComparison model) := do
  let source ← elaborateValueAsDateSource model sourceField endpoint
  pure { source with comparison, expected }

/-- Calendar operation selected by one checked `AddDays`, `AddMonths`, or `AddYears` placement. -/
inductive ValueAsDateShiftUnit where
  | days
  | months
  | years
  deriving Repr, DecidableEq

namespace ValueAsDateShiftUnit

/-- Apply the selected calendar rule without imposing the A12 full-Date floor on the landing. -/
def shift? (unit : ValueAsDateShiftUnit)
    (date : FullDate) (offset : Int) : Option CivilDate :=
  match unit with
  | .days => date.civil.addDays? offset
  | .months => date.civil.addMonths? offset
  | .years => date.civil.addYears? offset

end ValueAsDateShiftUnit

/-- One nested partial-Date calendar-shift result before any computed-target policy is applied. A civil landing can precede the A12 value floor and must remain an attempted value for the later target check. -/
inductive ValueAsDateShiftResult where
  | noValue
  | value (date : CivilDate)
  | nonRelevant
  | poison (cause : FormalCause)
  deriving Repr, DecidableEq

/-- Structural failure after both operation operands are semantically available. -/
inductive ValueAsDateShiftFault where
  | landingUnavailable
      (unit : ValueAsDateShiftUnit) (source : FullDate) (offset : Int)
  deriving Repr, DecidableEq

/-- One checked nested calendar shift that specializes the shared partial-Date source admission. -/
structure CheckedValueAsDateShift (model : FlatModel)
    extends CheckedValueAsDateSource model where
  unit : ValueAsDateShiftUnit

namespace CheckedValueAsDateShift

/-- Evaluate the source first and the numeric amount second, matching generated Java argument order. A reached formal poison therefore ends evaluation at its own operand; ordinary numeric domain failure reaches the calendar helper as no-value. -/
def evaluate (checked : CheckedValueAsDateShift model)
    (cell : CheckedCell
      (AdmittedPartiallyKnownDate checked.source.policy.partialMode))
    (amount : NumericComputationResult) :
    Except ValueAsDateShiftFault ValueAsDateShiftResult :=
  match checked.toCheckedValueAsDateSource.observe Phase.computation cell with
  | .unavailable cause => pure (.poison cause)
  | .empty =>
      match amount with
      | .poison cause => pure (.poison cause)
      | .domainFailure | .value _ => pure .noValue
  | .nonRelevant =>
      match amount with
      | .poison cause => pure (.poison cause)
      | .domainFailure | .value _ => pure .nonRelevant
  | .date date =>
      match amount with
      | .poison cause => pure (.poison cause)
      | .domainFailure => pure .noValue
      | .value value =>
          let offset := temporalShiftAmountToInt32 value
          match checked.unit.shift? date offset with
          | some landing => pure (.value landing)
          | none =>
              throw (.landingUnavailable checked.unit date offset)

/-- Check an exact stored-text source and evaluate it with one already reached numeric amount. -/
def evaluateRaw (checked : CheckedValueAsDateShift model)
    (raw : RawCell String) (amount : NumericComputationResult) :
    Except ValueAsDateShiftFault ValueAsDateShiftResult :=
  checked.evaluate
    (checked.toCheckedValueAsDateSource.checkSourceRaw raw) amount

end CheckedValueAsDateShift

/-- Resolve and certify one nonrepeatable nested partial-Date calendar shift. -/
def elaborateValueAsDateShift
    (model : FlatModel) (sourceField : FieldId)
    (endpoint : ValueAsDateEndpoint) (unit : ValueAsDateShiftUnit) :
    Except ValueAsDateElabError (CheckedValueAsDateShift model) := do
  let source ← elaborateValueAsDateSource model sourceField endpoint
  pure { source with unit }

/-- Which authored Date-difference operand is supplied by the partial-Date expression. Generated argument evaluation follows this order before the calendar helper runs. -/
inductive ValueAsDateDifferencePlacement where
  | left
  | right
  deriving Repr, DecidableEq

/-- One nested partial-Date month/year difference result. Cause-free non-relevance stays separate from the established numeric operand because fabricating a `FormalCause` would make it indistinguishable from a rejected read. -/
inductive ValueAsDateDifferenceResult where
  | operand (value : NumericOperand)
  | nonRelevant
  deriving Repr, DecidableEq

namespace ValueAsDateDifferenceResult

/-- Consume the nested result in a fixed-right numeric validation without collapsing non-relevance into a formal cause. -/
def evalFixedRight (result : ValueAsDateDifferenceResult)
    (op : NumericComparisonOp) (expected : Rat) : Verdict :=
  match result with
  | .operand value => op.evalFixedRight value expected
  | .nonRelevant => .unknown

end ValueAsDateDifferenceResult

/-- Structural refusal after both authored operands have been read and neither empty substitution nor non-relevance masks the unsupported calendar. -/
inductive ValueAsDateDifferenceFault where
  | unsupportedCalendar
  deriving Repr, DecidableEq

/-- One checked partial-Date placement in a completed-month or completed-year difference. The ordinary operand has already passed its existing Date-difference admission boundary. -/
structure CheckedValueAsDateDifference (model : FlatModel)
    extends CheckedValueAsDateSource model where
  unit : DateDifferenceUnit
  placement : ValueAsDateDifferencePlacement

namespace CheckedValueAsDateDifference

private def evaluateAvailable (checked : CheckedValueAsDateDifference model)
    (sourceObservation : ValueAsDateObservation)
    (other : DateDifferenceOperand) :
    Except ValueAsDateDifferenceFault ValueAsDateDifferenceResult :=
  match sourceObservation, other with
  | .nonRelevant, _ => pure .nonRelevant
  | .empty, _ | .date _, .empty =>
      pure (.operand (.value 0 .both))
  | .date _, .unsupportedCalendar =>
      throw .unsupportedCalendar
  | .date partialDate, .value otherDate =>
      let value :=
        match checked.placement with
        | .left =>
            checked.unit.between partialDate.civil.parts otherDate
        | .right =>
            checked.unit.between otherDate partialDate.civil.parts
      pure (.operand (.value value .fixed))
  | .unavailable cause, _ | _, .unavailable cause =>
      pure (.operand (.unknown cause))

/-- Evaluate formal reads in authored order, then apply the runtime helper's non-relevant, empty, calendar, and completed-period precedence. -/
def evaluate (checked : CheckedValueAsDateDifference model)
    (phase : Phase)
    (cell : CheckedCell
      (AdmittedPartiallyKnownDate checked.source.policy.partialMode))
    (other : DateDifferenceOperand) :
    Except ValueAsDateDifferenceFault ValueAsDateDifferenceResult :=
  let sourceObservation :=
    checked.toCheckedValueAsDateSource.observe phase cell
  match checked.placement with
  | .left =>
      match sourceObservation with
      | .unavailable cause => pure (.operand (.unknown cause))
      | _ =>
          match other with
          | .unavailable cause => pure (.operand (.unknown cause))
          | _ => checked.evaluateAvailable sourceObservation other
  | .right =>
      match other with
      | .unavailable cause => pure (.operand (.unknown cause))
      | _ =>
          match sourceObservation with
          | .unavailable cause => pure (.operand (.unknown cause))
          | _ => checked.evaluateAvailable sourceObservation other

/-- Check one exact stored-text partial source and preserve the already resolved ordinary operand. -/
def evaluateRaw (checked : CheckedValueAsDateDifference model)
    (phase : Phase) (raw : RawCell String)
    (other : DateDifferenceOperand) :
    Except ValueAsDateDifferenceFault ValueAsDateDifferenceResult :=
  checked.evaluate phase
    (checked.toCheckedValueAsDateSource.checkSourceRaw raw) other

end CheckedValueAsDateDifference

/-- Resolve and certify one partial-Date operand in a nonrepeatable month/year difference. -/
def elaborateValueAsDateDifference
    (model : FlatModel) (sourceField : FieldId)
    (endpoint : ValueAsDateEndpoint) (unit : DateDifferenceUnit)
    (placement : ValueAsDateDifferencePlacement) :
    Except ValueAsDateElabError (CheckedValueAsDateDifference model) := do
  let source ← elaborateValueAsDateSource model sourceField endpoint
  pure { source with unit, placement }

/-- Static refusal before a partial-Date consumer can select the model's concrete zone profile. -/
inductive ValueAsDateZonedElabError where
  | source (error : ValueAsDateElabError)
  | unsupportedZone (zoneId : String)
  deriving Repr, DecidableEq

/-- The checked partial-Date source plus its model-owned concrete zone profile. DateTime construction and calendar-day difference share this exact capability; neither may substitute a caller-selected zone. -/
structure CheckedZonedValueAsDateSource (model : FlatModel)
    extends CheckedValueAsDateSource model where
  profile : ModelZone.ConcreteProfile
  profileMatches :
    ModelZone.ConcreteProfile.ofId? source.timeZoneId = some profile

/-- Resolve one partial-Date endpoint and its model-owned concrete profile. -/
def elaborateZonedValueAsDateSource
    (model : FlatModel) (sourceField : FieldId)
    (endpoint : ValueAsDateEndpoint) :
    Except ValueAsDateZonedElabError
      (CheckedZonedValueAsDateSource model) := do
  let source ←
    elaborateValueAsDateSource model sourceField endpoint |>.mapError .source
  match hProfile :
      ModelZone.ConcreteProfile.ofId? source.source.timeZoneId with
  | none => throw (.unsupportedZone source.source.timeZoneId)
  | some profile =>
      pure { source with profile, profileMatches := hProfile }

/-- Result of combining one resolved partial-Date endpoint with an already checked Time observation. A real value retains whether an input was missing, because the kernel may construct a value that still produces omission polarity. A missing input and a present wall label rejected by the model zone both have no value, but only the former is not-given. -/
inductive ValueAsDateTimeResult where
  | noValue (notGiven : Bool)
  | value (localDateTime : LocalDateTime) (instant : Instant) (notGiven : Bool)
  | nonRelevant
  | unavailable (cause : FormalCause)
  deriving Repr, DecidableEq

/-- The Time-side reason domain shared by a checked field and resolved Time expression. A value retains missing provenance because date arithmetic can return a concrete clock while an empty numeric input still makes the result not-given. `noValue false` retains a fully present but impossible clock. -/
inductive ValueAsDateTimeTimeOperand where
  | noValue (notGiven : Bool)
  | value (time : TimeOfDay) (notGiven : Bool)
  | nonRelevant
  | unavailable (cause : FormalCause)
  deriving Repr, DecidableEq

namespace ValueAsDateTimeTimeOperand

/-- Project one direct checked Time field without losing its empty or formal state. -/
def ofObservation : CellObservation TimeOfDay → ValueAsDateTimeTimeOperand
  | .empty => .noValue true
  | .value time => .value time false
  | .unknown cause | .poison cause => .unavailable cause

end ValueAsDateTimeTimeOperand

namespace TimeConstructionResult

/-- Preserve resolved Time-construction reasons at the shared DateTime operand seam. -/
def asDateTimeOperand : TimeConstructionResult → ValueAsDateTimeTimeOperand
  | .value time => .value time false
  | .incomplete => .noValue true
  | .unreal => .noValue false
  | .nonRelevant => .nonRelevant
  | .unavailable cause => .unavailable cause

end TimeConstructionResult

namespace ValueAsDateTimeResult

/-- Consume one constructed result in an exact-instant fixed-right validation. No-value does not fire; non-relevance and formal unavailability both project to UNKNOWN without being identified with each other. -/
def evalFixedRight (result : ValueAsDateTimeResult)
    (op : TemporalComparisonOp) (expected : Instant) : Verdict :=
  match result with
  | .noValue _ => .notFired
  | .value _ instant notGiven =>
      op.evalInstant (.value instant (!notGiven)) (.value expected true)
  | .nonRelevant | .unavailable _ => .unknown

end ValueAsDateTimeResult

/-- DateTime construction uses the shared checked zoned partial-Date source without adding operation-specific static state. -/
abbrev CheckedValueAsDateTime := CheckedZonedValueAsDateSource

/-- Compatibility name for the shared zoned-source refusal. -/
abbrev ValueAsDateTimeElabError := ValueAsDateZonedElabError

namespace CheckedValueAsDateTime

private def combine (checked : CheckedValueAsDateTime model)
    (dateObservation : ValueAsDateObservation)
    (time : ValueAsDateTimeTimeOperand) : ValueAsDateTimeResult :=
  match dateObservation with
  | .unavailable cause => .unavailable cause
  | _ =>
      match time with
      | .unavailable cause => .unavailable cause
      | _ =>
          match dateObservation, time with
          | .nonRelevant, _ => .nonRelevant
          | _, .nonRelevant => .nonRelevant
          | .empty, _ => .noValue true
          | .date _, .noValue notGiven => .noValue notGiven
          | .date date, .value clock notGiven =>
              let localDateTime : LocalDateTime := { date, time := clock }
              match checked.profile.resolveLocal? localDateTime with
              | some instant => .value localDateTime instant notGiven
              | none => .noValue false
          | .unavailable cause, _ => .unavailable cause
          | _, .unavailable cause => .unavailable cause

/-- Read Date before one reason-bearing Time operand, then apply the runtime constructor's non-relevance, missingness, and zone-resolution distinctions. -/
def evaluateOperand (checked : CheckedValueAsDateTime model)
    (phase : Phase)
    (cell : CheckedCell
      (AdmittedPartiallyKnownDate checked.source.policy.partialMode))
    (time : ValueAsDateTimeTimeOperand) : ValueAsDateTimeResult :=
  checked.combine
    (checked.toCheckedValueAsDateSource.observe phase cell) time

/-- Compatibility entry for one direct typed Time observation. -/
def evaluate (checked : CheckedValueAsDateTime model)
    (phase : Phase)
    (cell : CheckedCell
      (AdmittedPartiallyKnownDate checked.source.policy.partialMode))
    (time : CellObservation TimeOfDay) : ValueAsDateTimeResult :=
  checked.evaluateOperand phase cell
    (ValueAsDateTimeTimeOperand.ofObservation time)

/-- Check one exact stored-text special Date while preserving the caller's already checked direct Time observation. -/
def evaluateRaw (checked : CheckedValueAsDateTime model)
    (phase : Phase) (raw : RawCell String)
    (time : CellObservation TimeOfDay) : ValueAsDateTimeResult :=
  checked.evaluate phase
    (checked.toCheckedValueAsDateSource.checkSourceRaw raw) time

/-- Check the bounded partial-Date source before invoking one caller-supplied Time operand
    thunk. This is the shared generated-order seam for complete-Time fields,
    `TimeFromDateTime`, and checked component prefixes. -/
def evaluateTimeOperandRaw (checked : CheckedValueAsDateTime model)
    (phase : Phase) (raw : RawCell String)
    (time : Unit → Except error ValueAsDateTimeTimeOperand) :
    Except error ValueAsDateTimeResult := do
  let dateCell := checked.toCheckedValueAsDateSource.checkSourceRaw raw
  match checked.toCheckedValueAsDateSource.observe phase dateCell with
  | .unavailable cause => pure (.unavailable cause)
  | _ =>
      let timeOperand ← time ()
      pure (checked.evaluateOperand phase dateCell timeOperand)

/-- Compose one already resolved `Time(...)` result through the shared reason-bearing operand seam. -/
def evaluateConstructionRaw (checked : CheckedValueAsDateTime model)
    (phase : Phase) (raw : RawCell String)
    (time : TimeConstructionResult) : ValueAsDateTimeResult :=
  checked.evaluateOperand phase
    (checked.toCheckedValueAsDateSource.checkSourceRaw raw)
    time.asDateTimeOperand

end CheckedValueAsDateTime

/-- Resolve one partial-Date endpoint and the model-owned concrete profile for bounded DateTime construction. -/
def elaborateValueAsDateTime
    (model : FlatModel) (sourceField : FieldId)
    (endpoint : ValueAsDateEndpoint) :
    Except ValueAsDateTimeElabError (CheckedValueAsDateTime model) := do
  elaborateZonedValueAsDateSource model sourceField endpoint

end A12Kernel
