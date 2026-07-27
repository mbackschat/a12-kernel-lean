import A12Kernel.Elaboration.TemporalTargetPolicy
import A12Kernel.Semantics.DateComparison
import A12Kernel.Semantics.Observation

/-! # Checked partial-Date `ValueAsDate`

This capsule retains every admitted stored Date omission, resolves a known-year interval only after `FirstDay` or `LastDay` is selected, and delegates the resulting full Date to the existing direct-comparison evaluator. An unknown year is retained as its own value and becomes non-relevant at the operation boundary rather than acquiring a fabricated year. Its bounded raw adapter accepts the two exact declaration formats already owned by temporal targets. Wider format syntax, detailed formal-error codes, Date arithmetic, DateTime construction, and repeatable addressing remain separate.
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

/-- One checked direct comparison whose source declaration, interval endpoint, operator, and literal cannot be replaced independently after elaboration. -/
structure CheckedValueAsDateComparison (model : FlatModel) where
  source : CheckedTemporalTargetPolicy model
  endpoint : ValueAsDateEndpoint
  comparison : TemporalComparisonOp
  expected : FullDate
  format : FullDateTargetFormat
  sourceIsDate : source.target.kind = .date
  sourceIsPartial : source.policy.partialMode ≠ .full
  formatMatches :
    FullDateTargetFormat.ofSource? source.policy.format = some format

namespace CheckedValueAsDateComparison

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
def checkSourceRaw (checked : CheckedValueAsDateComparison model)
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

/-- Evaluate one already parser-admitted stored value through the existing checked-cell observation and full-Date comparison paths. -/
def evaluate (checked : CheckedValueAsDateComparison model)
    (cell : CheckedCell
      (AdmittedPartiallyKnownDate checked.source.policy.partialMode)) : Verdict :=
  match (observeCell .validation cell).resolvePartiallyKnownDate checked.endpoint with
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
            comparison
            expected
            format
            sourceIsDate := hKind
            sourceIsPartial := hMode
            formatMatches := hFormat }
    else
      throw (.unsupportedPartialMode sourceField source.policy.partialMode)
  else
    throw (.sourceKind sourceField source.target.kind)

end A12Kernel
