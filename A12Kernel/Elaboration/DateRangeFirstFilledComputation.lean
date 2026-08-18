import A12Kernel.Elaboration.TemporalFirstFilledStarComputation
import A12Kernel.Semantics.TemporalTarget

/-! # Direct one-star DateRange `FirstFilledValue` computation -/

namespace A12Kernel

inductive DateRangeFirstFilledComputationElabError where
  | shape (cause : TemporalFirstFilledStarComputationElabError)
  deriving Repr, DecidableEq

/-- One fixed ISO/slash DateRange target and one direct single-level starred source of the same carrier. -/
structure CheckedDateRangeFirstFilledComputation (model : FlatModel) where
  private mk ::
  shape : CheckedTemporalFirstFilledStarComputation model .dateRangeIsoSlash

/-- Check the exact maintained DateRange computation shape without widening policy, operands, nesting, or document architecture. -/
def checkDateRangeFirstFilledComputation
    (model : FlatModel) (declaringGroup : GroupPath) (targetField : FieldId)
    (authored : SurfaceStarFieldPath) :
    Except DateRangeFirstFilledComputationElabError
      (CheckedDateRangeFirstFilledComputation model) := do
  let shape ← checkTemporalFirstFilledStarComputation
    model declaringGroup targetField authored .dateRangeIsoSlash
      |>.mapError .shape
  pure { shape }

/-- Project one checked DateRange cell into the typed root result consumed by the target policy. Source stored text is not selected. -/
def dateRangeFirstFilledCellAt
    (addressed : CheckedAddressedCell) : DateRangeComputationResult :=
  match observeCell .computation addressed.cell with
  | .value (.dateRange range) => .value range
  | .value _ => .poison .malformed
  | .empty => .noValue
  | .unknown cause | .poison cause => .poison cause

/-- Select the first present DateRange or reached formal cause; exhaustion keeps the no-value identity. -/
def evalDateRangeFirstFilledCells :
    List CheckedAddressedCell → DateRangeComputationResult
  | [] => .noValue
  | addressed :: remaining =>
      match dateRangeFirstFilledCellAt addressed with
      | .noValue => evalDateRangeFirstFilledCells remaining
      | result => result

inductive DateRangeFirstFilledComputationFault where
  | source (cause : CheckedStarDocumentError)
  | unresolvedEndpoint (range : DateRangeValue)
  deriving Repr, DecidableEq

namespace CheckedDateRangeFirstFilledComputation

/-- Execute through the single checked document, bridge the typed range into resolved full-Date endpoints, and render through the checked target policy. -/
def execute (operation : CheckedDateRangeFirstFilledComputation model)
    (input : CheckedDocument model) :
    Except DateRangeFirstFilledComputationFault DateRangeTargetOutcome := do
  let resolved ← operation.shape.source.resolveCheckedField input []
    |>.mapError .source
  match evalDateRangeFirstFilledCells resolved.cells with
  | .noValue => pure .noValue
  | .poison cause => pure (.poison cause)
  | .value range =>
      match range.toResolvedDateRange? with
      | none => throw (.unresolvedEndpoint range)
      | some resolvedRange =>
          pure (.accepted (DateRangeTargetFormat.isoSlash.render resolvedRange))

end CheckedDateRangeFirstFilledComputation

end A12Kernel
