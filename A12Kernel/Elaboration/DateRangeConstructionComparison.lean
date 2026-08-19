import A12Kernel.Elaboration.DateRangeBound
import A12Kernel.Elaboration.TemporalTargetPolicy
import A12Kernel.Elaboration.ValueAsDate
import A12Kernel.Semantics.DateRangeComparison

/-! # Checked DateRange construction comparison

This capsule certifies two nonrepeatable Date endpoints per `DateRange` construction, including exact `yyyy`, `yyyy-MM`, Base-Year-resolved `MM` and `MM-dd`, and yearless `MM` and `MM-dd` DateFragment profiles. It composes two component-compatible constructions or one full-Date construction with a canonical direct stored DateRange and reads each checked operand through one immutable document in authored order. Exact construction labels are completed by endpoint position and re-resolved under their declaration's model-zone profile; yearless pair execution retains only the authored components. Both delegate to the shared equality seam. Yearless construction-versus-stored execution, semantic-index endpoints, repeatable placement, computation, rendering, overlap, and bound extraction remain separate.
-/

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

/-- Recognize the checked endpoint profile; Base Year selects exact completion or retained yearless identity for `MM` and `MM-dd`. -/
def ofPolicy? (baseYear : Option Int) (policy : TemporalTargetPolicy) :
    Option DateRangeEndpointFormat :=
  match policy.partialMode with
  | .full => FullDateTargetFormat.ofSource? policy.format |>.map .full
  | .yearOptional =>
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
  | .dayOptional | .monthOptional => none

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

/-- Whether the endpoint belongs to the complete Date profile retained by mixed execution. -/
def isFull : DateRangeEndpointFormat → Bool
  | .full _ => true
  | .yearFragment | .yearMonthFragment | .monthFragment _
  | .monthDayFragment _ | .yearlessMonth | .yearlessMonthDay => false

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

structure CheckedDateRangeEndpoint (model : FlatModel) where
  checked : CheckedTemporalTargetPolicy model
  format : DateRangeEndpointFormat
  profile : ModelZone.ConcreteProfile
  targetIsDate : checked.target.kind = .date
  formatMatches : DateRangeEndpointFormat.ofPolicy? model.baseYear checked.policy = some format
  profileMatches : ModelZone.ConcreteProfile.ofId? checked.timeZoneId = some profile

inductive DateRangeEndpointElabError where
  | targetPolicy (cause : TemporalTargetElabError)
  | targetKind (target : FieldId) (actual : TemporalKind)
  | unsupportedPolicy (target : FieldId) (mode : TemporalPartialMode)
      (format : String)
  | unsupportedZone (zoneId : String)
  deriving Repr, DecidableEq

/-- Resolve one exact-or-yearless nonrepeatable endpoint profile without widening the scalar Date target owner. -/
def elaborateDateRangeEndpoint (model : FlatModel) (field : FieldId) :
    Except DateRangeEndpointElabError (CheckedDateRangeEndpoint model) := do
  let checked ← elaborateTemporalTargetPolicy model field |>.mapError .targetPolicy
  if hKind : checked.target.kind = .date then
    match hFormat : DateRangeEndpointFormat.ofPolicy? model.baseYear checked.policy with
    | none => throw (.unsupportedPolicy field checked.policy.partialMode checked.policy.format)
    | some format =>
        match hProfile : ModelZone.ConcreteProfile.ofId? checked.timeZoneId with
        | none => throw (.unsupportedZone checked.timeZoneId)
        | some profile => pure {
            checked
            format
            profile
            targetIsDate := hKind
            formatMatches := hFormat
            profileMatches := hProfile }
  else
    throw (.targetKind field checked.target.kind)

structure CheckedDateRangeConstruction (model : FlatModel) where
  start : CheckedDateRangeEndpoint model
  finish : CheckedDateRangeEndpoint model
  componentsMatch : start.format.sameComponents finish.format = true

inductive DateRangeConstructionElabError where
  | start (cause : DateRangeEndpointElabError)
  | finish (cause : DateRangeEndpointElabError)
  | componentMismatch (start finish : DateRangeEndpointFormat)
  deriving Repr, DecidableEq

/-- Certify one pair of construction endpoints once for every checked comparison consumer. -/
def elaborateDateRangeConstruction (model : FlatModel)
    (start finish : FieldId) :
    Except DateRangeConstructionElabError
      (CheckedDateRangeConstruction model) := do
  let checkedStart ← elaborateDateRangeEndpoint model start |>.mapError .start
  let checkedFinish ← elaborateDateRangeEndpoint model finish |>.mapError .finish
  if hComponents : checkedStart.format.sameComponents checkedFinish.format then
    pure {
      start := checkedStart
      finish := checkedFinish
      componentsMatch := hComponents }
  else
    throw (.componentMismatch checkedStart.format checkedFinish.format)

inductive DateRangeConstructionComparisonElabError where
  | left (cause : DateRangeConstructionElabError)
  | right (cause : DateRangeConstructionElabError)
  | componentMismatch (left right : DateRangeEndpointFormat)
  deriving Repr, DecidableEq

structure CheckedDateRangeConstructionComparison (model : FlatModel) where
  left : CheckedDateRangeConstruction model
  right : CheckedDateRangeConstruction model
  comparison : EqualityOp
  componentsMatch : left.start.format.sameComponents right.start.format = true

/-- Certify all four endpoint declarations and the cross-construction component invariant while retaining the authored comparison. -/
def elaborateDateRangeConstructionComparison (model : FlatModel)
    (leftStart leftFinish rightStart rightFinish : FieldId)
    (comparison : EqualityOp) :
    Except DateRangeConstructionComparisonElabError
      (CheckedDateRangeConstructionComparison model) := do
  let left ← elaborateDateRangeConstruction model leftStart leftFinish
    |>.mapError .left
  let right ← elaborateDateRangeConstruction model rightStart rightFinish
    |>.mapError .right
  if hComponents : left.start.format.sameComponents right.start.format then
    pure {
      left
      right
      comparison
      componentsMatch := hComponents }
  else
    throw (.componentMismatch left.start.format right.start.format)

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

/-- Structural failure outside the phase-sensitive endpoint observations. -/
inductive DateRangeConstructionFault where
  | document (cause : CheckedDocumentError)
  | endpointValueKind (source : FieldId)
  | endpointDateUnavailable (source : FieldId) (value : DateValue)
  deriving Repr, DecidableEq

namespace CheckedDateRangeConstruction

private def evaluateEndpoint (source : CheckedDateRangeEndpoint model)
    (bound : DateRangeBound) (phase : Phase) (input : CheckedDocument model) :
    Except DateRangeConstructionFault
      (CellObservation DateRangeConstructionEndpointValue) := do
  let field := source.checked.target.id
  let cell ← input.read { field, path := [] } |>.mapError .document
  match observeCell phase cell with
  | .empty => pure .empty
  | .value (.temporal (.date value)) =>
      match source.format with
      | .yearlessMonth =>
          match DateParts.daysInMonth? 2000 value.parts.month with
          | some _ => pure (.value (.month value.parts.month))
          | none => throw (.endpointDateUnavailable field value)
      | .yearlessMonthDay =>
          match FullDate.ofYmd? 2000 value.parts.month value.parts.day with
          | some _ => pure (.value (.monthDay {
              month := value.parts.month
              day := value.parts.day }))
          | none => throw (.endpointDateUnavailable field value)
      | format =>
          match format.complete? bound value.parts with
          | none => throw (.endpointDateUnavailable field value)
          | some date =>
              let instant? := (LocalDateTime.ofDateHms? date 0 0 0).bind
                source.profile.resolveLocal?
              match instant? with
              | some instant => pure (.value (.exact {
                  instant
                  parts := date.civil.parts
                  basis := .storedGregorian }))
              | none => throw (.endpointDateUnavailable field value)
  | .value _ => throw (.endpointValueKind field)
  | .unknown cause => pure (.unknown cause)
  | .poison cause => pure (.poison cause)

/-- Read each certified endpoint once from one immutable checked document. -/
def evaluate (construction : CheckedDateRangeConstruction model)
    (phase : Phase) (input : CheckedDocument model) :
    Except DateRangeConstructionFault DateRangeConstructionObservation := do
  let start ← evaluateEndpoint construction.start .start phase input
  let finish ← evaluateEndpoint construction.finish .finish phase input
  pure { start, finish }

end CheckedDateRangeConstruction

/-- Rich checked result retaining both constructions beside their projected verdict. -/
structure DateRangeConstructionComparisonResult where
  left : DateRangeConstructionObservation
  right : DateRangeConstructionObservation
  verdict : Verdict
  deriving Repr, DecidableEq

namespace CheckedDateRangeConstructionComparison

/-- Compare internally read observations without discarding endpoint identity or availability. -/
private def evaluateObserved (operation : CheckedDateRangeConstructionComparison model)
    (left right : DateRangeConstructionObservation) :
    DateRangeConstructionComparisonResult := {
  left
  right
  verdict := operation.comparison.evalDateRangeCellValues
    left.comparisonOperand right.comparisonOperand }

/-- Read both checked constructions in validation phase from the same immutable document and evaluate their exact-or-yearless endpoint identity. -/
def evaluate (operation : CheckedDateRangeConstructionComparison model)
    (input : CheckedDocument model) :
    Except DateRangeConstructionFault
      DateRangeConstructionComparisonResult := do
  let left ← operation.left.evaluate .validation input
  let right ← operation.right.evaluate .validation input
  pure (operation.evaluateObserved left right)

end CheckedDateRangeConstructionComparison

/-! ## Construction-versus-stored execution -/

inductive DateRangeConstructionStoredComparisonElabError where
  | construction (cause : DateRangeConstructionElabError)
  | unsupportedConstructionProfile (start finish : DateRangeEndpointFormat)
  | stored (cause : DirectDateRangeElabError)
  deriving Repr, DecidableEq

/-- One construction and one direct stored DateRange, retaining their authored order. -/
structure CheckedDateRangeConstructionStoredComparison (model : FlatModel) where
  construction : CheckedDateRangeConstruction model
  stored : CheckedDirectDateRange model
  position : DateRangeConstructionPosition
  comparison : EqualityOp
  constructionIsFull : construction.start.format.isFull = true

/-- Certify both full-Date mixed operands in authored order without introducing a second source or comparison representation. -/
def elaborateDateRangeConstructionStoredComparison (model : FlatModel)
    (start finish stored : FieldId) (position : DateRangeConstructionPosition)
    (comparison : EqualityOp) :
    Except DateRangeConstructionStoredComparisonElabError
      (CheckedDateRangeConstructionStoredComparison model) :=
  match position with
  | .left => do
      let construction ← elaborateDateRangeConstruction model start finish
        |>.mapError .construction
      if hFull : construction.start.format.isFull then
        let stored ← elaborateDirectDateRange model stored |>.mapError .stored
        pure { construction, stored, position, comparison, constructionIsFull := hFull }
      else
        throw (.unsupportedConstructionProfile
          construction.start.format construction.finish.format)
  | .right => do
      let stored ← elaborateDirectDateRange model stored |>.mapError .stored
      let construction ← elaborateDateRangeConstruction model start finish
        |>.mapError .construction
      if hFull : construction.start.format.isFull then
        pure { construction, stored, position, comparison, constructionIsFull := hFull }
      else
        throw (.unsupportedConstructionProfile
          construction.start.format construction.finish.format)

inductive DateRangeConstructionStoredComparisonFault where
  | construction (cause : DateRangeConstructionFault)
  | stored (cause : DirectDateRangeFault)
  deriving Repr, DecidableEq

/-- Rich mixed result retaining authored position and both exact operand observations. -/
structure DateRangeConstructionStoredComparisonResult where
  construction : DateRangeConstructionObservation
  stored : CellObservation DateRangeValue
  position : DateRangeConstructionPosition
  verdict : Verdict
  deriving Repr, DecidableEq

namespace CheckedDateRangeConstructionStoredComparison

/-- Lift the stored exact range into the shared cell comparison domain. -/
private def storedComparisonOperand : CellObservation DateRangeValue →
    SimpleComparisonOperand DateRangeCellValue
  | .empty => .notEvaluated
  | .value value => .value (.exact value) true
  | .unknown cause | .poison cause => .unknown cause

/-- Compare internally read mixed observations through the shared exact-instant equality seam. -/
private def evaluateObserved
    (operation : CheckedDateRangeConstructionStoredComparison model)
    (construction : DateRangeConstructionObservation)
    (stored : CellObservation DateRangeValue) :
    DateRangeConstructionStoredComparisonResult := {
  construction
  stored
  position := operation.position
  verdict := match operation.position with
    | .left => operation.comparison.evalDateRangeCellValues
        construction.comparisonOperand (storedComparisonOperand stored)
    | .right => operation.comparison.evalDateRangeCellValues
        (storedComparisonOperand stored) construction.comparisonOperand }

/-- Read both operands from one immutable document in authored order, preserving every observation beside the verdict. -/
def evaluate (operation : CheckedDateRangeConstructionStoredComparison model)
    (input : CheckedDocument model) :
    Except DateRangeConstructionStoredComparisonFault
      DateRangeConstructionStoredComparisonResult :=
  match operation.position with
  | .left => do
      let construction ← operation.construction.evaluate .validation input
        |>.mapError .construction
      let stored ← operation.stored.evaluate .validation input
        |>.mapError .stored
      pure (operation.evaluateObserved construction stored)
  | .right => do
      let stored ← operation.stored.evaluate .validation input
        |>.mapError .stored
      let construction ← operation.construction.evaluate .validation input
        |>.mapError .construction
      pure (operation.evaluateObserved construction stored)

end CheckedDateRangeConstructionStoredComparison

end A12Kernel
