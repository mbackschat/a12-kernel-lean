import A12Kernel.Elaboration.CheckedDocument
import A12Kernel.Elaboration.TemporalTargetPolicy
import A12Kernel.Semantics.DateRangeComparison

/-! # Checked full-Date construction comparison

This capsule certifies two nonrepeatable full-Date endpoints per `DateRange` construction, reads all four endpoints through one immutable checked document, and re-resolves each decoded label under its declaration's model-zone profile before retaining the exact constructed observations. Equality and inequality delegate to the shared DateRange comparison seam. DateFragment completion, semantic-index endpoints, repeatable placement, computation, rendering, overlap, and bound extraction remain separate.
-/

namespace A12Kernel

structure CheckedDateRangeConstruction (model : FlatModel) where
  start : CheckedFullDateTarget model
  finish : CheckedFullDateTarget model

inductive DateRangeConstructionComparisonElabError where
  | leftStart (cause : FullDateTargetElabError)
  | leftFinish (cause : FullDateTargetElabError)
  | rightStart (cause : FullDateTargetElabError)
  | rightFinish (cause : FullDateTargetElabError)
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
  let checkedLeftStart ← elaborateFullDateTarget model leftStart
    |>.mapError .leftStart
  let checkedLeftFinish ← elaborateFullDateTarget model leftFinish
    |>.mapError .leftFinish
  let checkedRightStart ← elaborateFullDateTarget model rightStart
    |>.mapError .rightStart
  let checkedRightFinish ← elaborateFullDateTarget model rightFinish
    |>.mapError .rightFinish
  pure {
    left := { start := checkedLeftStart, finish := checkedLeftFinish }
    right := { start := checkedRightStart, finish := checkedRightFinish }
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

end A12Kernel
