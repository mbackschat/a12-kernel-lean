import A12Kernel.Elaboration.TemporalFirstFilledStarComputation
import A12Kernel.Elaboration.TimeComputation

/-! # Direct one-star Time `FirstFilledValue` computation -/

namespace A12Kernel

inductive TimeFirstFilledComputationElabError where
  | shape (cause : TemporalFirstFilledStarComputationElabError)
  | targetPolicy (cause : TimeTargetElabError)
  deriving Repr, DecidableEq

/-- One fixed `HH:mm:ss` Time target and one direct single-level starred source of the same bounded carrier. -/
structure CheckedTimeFirstFilledComputation (model : FlatModel) where
  private mk ::
  shape : CheckedTemporalFirstFilledStarComputation model .timeHms
  targetPolicy : CheckedTimeTarget model

/-- Check the bounded Time computation shape. Wider formats, policies, operands, nesting, validation use, and materialized-document reconstruction remain outside this boundary. -/
def checkTimeFirstFilledComputation
    (model : FlatModel) (declaringGroup : GroupPath) (targetField : FieldId)
    (authored : SurfaceStarFieldPath) :
    Except TimeFirstFilledComputationElabError
      (CheckedTimeFirstFilledComputation model) := do
  let shape ← checkTemporalFirstFilledStarComputation
    model declaringGroup targetField authored .timeHms
      |>.mapError .shape
  let targetPolicy ← elaborateTimeTarget model targetField
    |>.mapError .targetPolicy
  pure { shape, targetPolicy }

/-- Project one checked Time cell into the clock-only result consumed by the existing target policy. Neither stored text nor the runtime transport instant enters this boundary. -/
def timeFirstFilledCellAt
    (addressed : CheckedAddressedCell) : TimeComputationResult :=
  match observeCell .computation addressed.cell with
  | .value (.temporal (.time _ clock)) => .value clock
  | .value _ => .poison .malformed
  | .empty => .noValue
  | .unknown cause | .poison cause => .poison cause

/-- Select the first present Time or reached formal cause; exhaustion keeps the Time no-value identity. -/
def evalTimeFirstFilledCells :
    List CheckedAddressedCell → TimeComputationResult
  | [] => .noValue
  | addressed :: remaining =>
      match timeFirstFilledCellAt addressed with
      | .noValue => evalTimeFirstFilledCells remaining
      | result => result

namespace CheckedTimeFirstFilledComputation

/-- Execute the checked source over immutable rows, then let the existing Time target render the selected clock. -/
def execute (operation : CheckedTimeFirstFilledComputation model)
    (input : CheckedDocument model) :
    Except CheckedStarDocumentError TimeTargetOutcome := do
  let resolved ← operation.shape.source.resolveCheckedField input []
  pure (operation.targetPolicy.evaluate
    (evalTimeFirstFilledCells resolved.cells))

/-- Execute and classify the one checked FirstFilled outcome against the same immutable source document. Residual messages remain already-classified opaque input. -/
def executeResult (operation : CheckedTimeFirstFilledComputation model)
    (input : CheckedDocument model)
    (residualMessages : List ResidualMessage) :
    Except CheckedStarDocumentError
      (TimeComputationRunView ResidualMessage) := do
  let outcome ← operation.execute input
  pure (TimeComputationRunView.fromOutcomes input residualMessages
    [(operation.targetPolicy.checked.target.id, outcome)])

end CheckedTimeFirstFilledComputation

end A12Kernel
