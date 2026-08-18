import A12Kernel.Elaboration.TemporalFirstFilledStarComputation
import A12Kernel.Elaboration.TemporalTargetPolicy

/-! # Direct one-star DateTime `FirstFilledValue` computation -/

namespace A12Kernel

inductive DateTimeFirstFilledComputationElabError where
  | shape (cause : TemporalFirstFilledStarComputationElabError)
  | targetPolicy (cause : DateTimeTargetElabError)
  deriving Repr, DecidableEq

/-- One fixed ISO whole-second DateTime target and one direct single-level starred source of the same carrier. -/
structure CheckedDateTimeFirstFilledComputation (model : FlatModel) where
  private mk ::
  shape : CheckedTemporalFirstFilledStarComputation model .dateTimeIso
  targetPolicy : CheckedDateTimeTarget model

/-- Check the bounded DateTime computation shape. Alternate formats, operands, nesting, validation use, and application remain outside this boundary. -/
def checkDateTimeFirstFilledComputation
    (model : FlatModel) (declaringGroup : GroupPath) (targetField : FieldId)
    (authored : SurfaceStarFieldPath) :
    Except DateTimeFirstFilledComputationElabError (CheckedDateTimeFirstFilledComputation model) := do
  let shape ← checkTemporalFirstFilledStarComputation model declaringGroup targetField authored .dateTimeIso |>.mapError .shape
  let targetPolicy ← elaborateDateTimeTarget model targetField |>.mapError .targetPolicy
  pure { shape, targetPolicy }

/-- Project one checked DateTime cell to its exact instant before model-zone target rendering. -/
def dateTimeFirstFilledCellAt (addressed : CheckedAddressedCell) : TemporalComputationResult :=
  match observeCell .computation addressed.cell with
  | .value (.temporal (.dateTime instant _ _ _)) => .value instant
  | .value _ => .poison .malformed
  | .empty => .noValue
  | .unknown cause | .poison cause => .poison cause

/-- Select the first present exact instant or reached formal cause; exhaustion keeps the temporal no-value identity. -/
def evalDateTimeFirstFilledCells : List CheckedAddressedCell → TemporalComputationResult
  | [] => .noValue
  | addressed :: remaining =>
      match dateTimeFirstFilledCellAt addressed with
      | .noValue => evalDateTimeFirstFilledCells remaining
      | result => result

inductive DateTimeFirstFilledComputationFault where
  | source (cause : CheckedStarDocumentError)
  | target (cause : DateTimeTargetEvaluationFault)
  deriving Repr, DecidableEq

namespace CheckedDateTimeFirstFilledComputation

/-- Execute the checked source over immutable rows and render the selected instant through the existing DateTime target policy. -/
def execute (operation : CheckedDateTimeFirstFilledComputation model) (input : CheckedDocument model) :
    Except DateTimeFirstFilledComputationFault DateTimeTargetOutcome := do
  let resolved ← operation.shape.source.resolveCheckedField input [] |>.mapError .source
  operation.targetPolicy.evaluate (evalDateTimeFirstFilledCells resolved.cells) |>.mapError .target

end CheckedDateTimeFirstFilledComputation

end A12Kernel
