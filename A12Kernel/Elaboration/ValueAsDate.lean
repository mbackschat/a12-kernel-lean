import A12Kernel.Elaboration.TemporalTargetPolicy
import A12Kernel.Semantics.DateComparison
import A12Kernel.Semantics.Observation

/-! # Checked day-optional `ValueAsDate`

This capsule retains a stored Date whose literal day was omitted, resolves that omission only after `FirstDay` or `LastDay` is selected, and delegates the resulting full Date to the existing direct-comparison evaluator. It admits one ordinary nonrepeatable `DAY_OPTIONAL` Date declaration with an exact supported format. Month/year omission, Date arithmetic, DateTime construction, repeatable addressing, and parsing stored text remain separate.
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

/-- One parser-admitted stored value for a `DAY_OPTIONAL` Date declaration. The constructor records whether the source contained a real day or the literal omission marker. -/
inductive DayOptionalDate where
  | full (date : FullDate)
  | omittedDay (date : OmittedDayDate)
  deriving Repr, DecidableEq

namespace DayOptionalDate

/-- Construct the omitted-day variant without exposing the interval constructor. -/
def ofOmittedDay? (year : Int) (month : Nat) : Option DayOptionalDate :=
  (OmittedDayDate.ofYearMonth? year month).map .omittedDay

/-- A full stored value denotes itself; an omitted value selects the authored interval boundary. -/
def resolve : DayOptionalDate → ValueAsDateEndpoint → FullDate
  | .full date, _ => date
  | .omittedDay date, endpoint => date.resolve endpoint

end DayOptionalDate

namespace CellObservation

/-- Preserve validation availability while resolving only a present day-optional value. -/
def resolveDayOptional
    (observation : CellObservation DayOptionalDate)
    (endpoint : ValueAsDateEndpoint) : CellObservation FullDate :=
  match observation with
  | .empty => .empty
  | .value date => .value (date.resolve endpoint)
  | .unknown cause => .unknown cause
  | .poison cause => .poison cause

end CellObservation

/-- Static refusal before the bounded day-optional direct-comparison consumer can execute. -/
inductive ValueAsDateElabError where
  | sourcePolicy (error : TemporalTargetElabError)
  | sourceKind (source : FieldId) (actual : TemporalKind)
  | unsupportedPartialMode (source : FieldId) (actual : TemporalPartialMode)
  | unsupportedFormat (source : FieldId) (format : String)
  deriving Repr, DecidableEq

/-- One checked direct comparison whose source declaration, omitted-day endpoint, operator, and literal cannot be replaced independently after elaboration. -/
structure CheckedValueAsDateComparison (model : FlatModel) where
  source : CheckedTemporalTargetPolicy model
  endpoint : ValueAsDateEndpoint
  comparison : TemporalComparisonOp
  expected : FullDate
  format : FullDateTargetFormat
  sourceIsDate : source.target.kind = .date
  sourceIsDayOptional : source.policy.partialMode = .dayOptional
  formatMatches :
    FullDateTargetFormat.ofSource? source.policy.format = some format

namespace CheckedValueAsDateComparison

/-- Evaluate one already parser-admitted stored value through the existing checked-cell observation and full-Date comparison paths. -/
def evaluate (checked : CheckedValueAsDateComparison model)
    (cell : CheckedCell DayOptionalDate) : Verdict :=
  checked.comparison.evalObserved
    ((observeCell .validation cell).resolveDayOptional checked.endpoint)
    (.value checked.expected)

end CheckedValueAsDateComparison

/-- Resolve and certify the first executable `ValueAsDate` slice. The kernel admits wider partial precisions, but this entry point rejects them explicitly until their completion rules are separately represented. -/
def elaborateValueAsDateComparison
    (model : FlatModel) (sourceField : FieldId)
    (endpoint : ValueAsDateEndpoint)
    (comparison : TemporalComparisonOp) (expected : FullDate) :
    Except ValueAsDateElabError (CheckedValueAsDateComparison model) := do
  let source ←
    elaborateTemporalTargetPolicy model sourceField |>.mapError .sourcePolicy
  if hKind : source.target.kind = .date then
    if hMode : source.policy.partialMode = .dayOptional then
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
            sourceIsDayOptional := hMode
            formatMatches := hFormat }
    else
      throw (.unsupportedPartialMode sourceField source.policy.partialMode)
  else
    throw (.sourceKind sourceField source.target.kind)

end A12Kernel
