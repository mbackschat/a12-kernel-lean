import A12Kernel.Elaboration.DateRangeBound
import A12Kernel.Elaboration.TemporalTargetPolicy
import A12Kernel.Semantics.DateRangeComparison

/-! # Checked full-Date construction comparison

This capsule certifies two nonrepeatable full-Date endpoints per `DateRange` construction, composes either two constructions or one construction with a canonical direct stored DateRange, and reads each checked operand through one immutable document in authored order. Construction labels are re-resolved under their declaration's model-zone profile before the exact observations delegate to the shared equality seam. DateFragment completion, semantic-index endpoints, repeatable placement, computation, rendering, overlap, and bound extraction remain separate.
-/

namespace A12Kernel

structure CheckedDateRangeConstruction (model : FlatModel) where
  start : CheckedFullDateTarget model
  finish : CheckedFullDateTarget model

inductive DateRangeConstructionElabError where
  | start (cause : FullDateTargetElabError)
  | finish (cause : FullDateTargetElabError)
  deriving Repr, DecidableEq

/-- Certify one pair of construction endpoints once for every checked comparison consumer. -/
def elaborateDateRangeConstruction (model : FlatModel)
    (start finish : FieldId) :
    Except DateRangeConstructionElabError
      (CheckedDateRangeConstruction model) := do
  let checkedStart ← elaborateFullDateTarget model start |>.mapError .start
  let checkedFinish ← elaborateFullDateTarget model finish |>.mapError .finish
  pure { start := checkedStart, finish := checkedFinish }

inductive DateRangeConstructionComparisonElabError where
  | left (cause : DateRangeConstructionElabError)
  | right (cause : DateRangeConstructionElabError)
  deriving Repr, DecidableEq

structure CheckedDateRangeConstructionComparison (model : FlatModel) where
  left : CheckedDateRangeConstruction model
  right : CheckedDateRangeConstruction model
  comparison : EqualityOp

/-- Certify all four endpoint declarations while retaining the authored comparison. -/
def elaborateDateRangeConstructionComparison (model : FlatModel)
    (leftStart leftFinish rightStart rightFinish : FieldId)
    (comparison : EqualityOp) :
    Except DateRangeConstructionComparisonElabError
      (CheckedDateRangeConstructionComparison model) := do
  let left ← elaborateDateRangeConstruction model leftStart leftFinish
    |>.mapError .left
  let right ← elaborateDateRangeConstruction model rightStart rightFinish
    |>.mapError .right
  pure {
    left
    right
    comparison }

/-- Both endpoint observations retained for Execute and Explain. -/
structure DateRangeConstructionObservation where
  start : CellObservation DateValue
  finish : CellObservation DateValue
  deriving Repr, DecidableEq

namespace DateRangeConstructionObservation

/-- Classify one construction for comparison. Formal unavailability dominates emptiness; only two present endpoints form a value. -/
def comparisonOperand (observation : DateRangeConstructionObservation) :
    SimpleComparisonOperand DateRangeValue :=
  match observation.start, observation.finish with
  | .unknown cause, _ | .poison cause, _ => .unknown cause
  | _, .unknown cause | _, .poison cause => .unknown cause
  | .empty, _ | _, .empty => .notEvaluated
  | .value start, .value finish => .value { start, finish } true

end DateRangeConstructionObservation

/-- Structural failure outside the phase-sensitive endpoint observations. -/
inductive DateRangeConstructionFault where
  | document (cause : CheckedDocumentError)
  | endpointValueKind (source : FieldId)
  | endpointDateUnavailable (source : FieldId) (value : DateValue)
  deriving Repr, DecidableEq

namespace CheckedDateRangeConstruction

private def evaluateEndpoint (source : CheckedFullDateTarget model)
    (phase : Phase) (input : CheckedDocument model) :
    Except DateRangeConstructionFault (CellObservation DateValue) := do
  let field := source.checked.target.id
  let cell ← input.read { field, path := [] } |>.mapError .document
  match observeCell phase cell with
  | .empty => pure .empty
  | .value (.temporal (.date value)) =>
      let instant? := value.toFullDate? |>.bind fun date =>
        (LocalDateTime.ofDateHms? date 0 0 0).bind source.profile.resolveLocal?
      match instant? with
      | some instant => pure (.value { value with instant, basis := .storedGregorian })
      | none => throw (.endpointDateUnavailable field value)
  | .value _ => throw (.endpointValueKind field)
  | .unknown cause => pure (.unknown cause)
  | .poison cause => pure (.poison cause)

/-- Read each certified endpoint once from one immutable checked document. -/
def evaluate (construction : CheckedDateRangeConstruction model)
    (phase : Phase) (input : CheckedDocument model) :
    Except DateRangeConstructionFault DateRangeConstructionObservation := do
  let start ← evaluateEndpoint construction.start phase input
  let finish ← evaluateEndpoint construction.finish phase input
  pure { start, finish }

end CheckedDateRangeConstruction

/-- Rich checked result retaining both constructions beside their projected verdict. -/
structure DateRangeConstructionComparisonResult where
  left : DateRangeConstructionObservation
  right : DateRangeConstructionObservation
  verdict : Verdict
  deriving Repr, DecidableEq

namespace CheckedDateRangeConstructionComparison

/-- Compare already-read observations without discarding endpoint identity or availability. -/
def evaluateObserved (operation : CheckedDateRangeConstructionComparison model)
    (left right : DateRangeConstructionObservation) :
    DateRangeConstructionComparisonResult := {
  left
  right
  verdict := operation.comparison.evalDateRangeValues
    left.comparisonOperand right.comparisonOperand }

/-- Read both checked constructions in validation phase from the same immutable document and evaluate their exact endpoint identity. -/
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
  | stored (cause : DirectDateRangeElabError)
  deriving Repr, DecidableEq

/-- One construction and one direct stored DateRange, retaining their authored order. -/
structure CheckedDateRangeConstructionStoredComparison (model : FlatModel) where
  construction : CheckedDateRangeConstruction model
  stored : CheckedDirectDateRange model
  position : DateRangeConstructionPosition
  comparison : EqualityOp

/-- Certify both mixed operands in authored order without introducing a second source or comparison representation. -/
def elaborateDateRangeConstructionStoredComparison (model : FlatModel)
    (start finish stored : FieldId) (position : DateRangeConstructionPosition)
    (comparison : EqualityOp) :
    Except DateRangeConstructionStoredComparisonElabError
      (CheckedDateRangeConstructionStoredComparison model) :=
  match position with
  | .left => do
      let construction ← elaborateDateRangeConstruction model start finish
        |>.mapError .construction
      let stored ← elaborateDirectDateRange model stored |>.mapError .stored
      pure { construction, stored, position, comparison }
  | .right => do
      let stored ← elaborateDirectDateRange model stored |>.mapError .stored
      let construction ← elaborateDateRangeConstruction model start finish
        |>.mapError .construction
      pure { construction, stored, position, comparison }

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

/-- Compare already-read mixed observations through the shared exact-instant equality seam. -/
def evaluateObserved
    (operation : CheckedDateRangeConstructionStoredComparison model)
    (construction : DateRangeConstructionObservation)
    (stored : CellObservation DateRangeValue) :
    DateRangeConstructionStoredComparisonResult := {
  construction
  stored
  position := operation.position
  verdict := match operation.position with
    | .left => operation.comparison.evalDateRangeValues
        construction.comparisonOperand stored.asValidationSimpleOperand
    | .right => operation.comparison.evalDateRangeValues
        stored.asValidationSimpleOperand construction.comparisonOperand }

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
