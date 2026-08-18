import A12Kernel.Elaboration.TemporalFirstFilledStarComputation
import A12Kernel.Elaboration.TemporalTargetPolicy

/-! # Direct one-star full-Date `FirstFilledValue` computation -/

namespace A12Kernel

inductive FullDateFirstFilledComputationElabError where
  | shape (cause : TemporalFirstFilledStarComputationElabError)
  | targetPolicy (cause : FullDateTargetElabError)
  deriving Repr, DecidableEq

/-- One fixed `yyyy-MM-dd` full-Date target and one direct single-level starred source of the same bounded carrier. -/
structure CheckedFullDateFirstFilledComputation (model : FlatModel) where
  private mk ::
  shape : CheckedTemporalFirstFilledStarComputation model .fullDateIso
  targetPolicy : CheckedFullDateTarget model

/-- Check the exact externally measured full-Date computation shape. Wider formats, policies, operands, nesting, validation use, and application remain outside this boundary. -/
def checkFullDateFirstFilledComputation
    (model : FlatModel) (declaringGroup : GroupPath) (targetField : FieldId)
    (authored : SurfaceStarFieldPath) :
    Except FullDateFirstFilledComputationElabError
      (CheckedFullDateFirstFilledComputation model) := do
  let shape ← checkTemporalFirstFilledStarComputation
    model declaringGroup targetField authored .fullDateIso
      |>.mapError .shape
  let targetPolicy ← elaborateFullDateTarget model targetField
    |>.mapError .targetPolicy
  pure { shape, targetPolicy }

/-- Project one checked full-Date cell into the typed root computation result consumed by the target policy. Stored text is deliberately not selected here, so the account does not choose copy over decode/render. -/
def fullDateFirstFilledCellAt
    (addressed : CheckedAddressedCell) : TemporalComputationResult :=
  match observeCell .computation addressed.cell with
  | .value (.temporal (.date date)) => .value date.instant
  | .value _ => .poison .malformed
  | .empty => .noValue
  | .unknown cause | .poison cause => .poison cause

/-- Select the first present full Date or reached formal cause; exhaustion keeps the temporal no-value identity. -/
def evalFullDateFirstFilledCells :
    List CheckedAddressedCell → TemporalComputationResult
  | [] => .noValue
  | addressed :: remaining =>
      match fullDateFirstFilledCellAt addressed with
      | .noValue => evalFullDateFirstFilledCells remaining
      | result => result

inductive FullDateFirstFilledComputationFault where
  | source (cause : CheckedStarDocumentError)
  | target (cause : FullDateTargetEvaluationFault)
  deriving Repr, DecidableEq

namespace CheckedFullDateFirstFilledComputation

/-- Execute the checked source over immutable rows, then let the existing target policy render and classify the selected typed Date. -/
def execute (operation : CheckedFullDateFirstFilledComputation model)
    (input : CheckedDocument model) :
    Except FullDateFirstFilledComputationFault FullDateTargetOutcome := do
  let resolved ← operation.shape.source.resolveCheckedField input []
    |>.mapError .source
  operation.targetPolicy.evaluate (evalFullDateFirstFilledCells resolved.cells)
    |>.mapError .target

end CheckedFullDateFirstFilledComputation

end A12Kernel
