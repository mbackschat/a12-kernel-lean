import A12Kernel.Elaboration.TemporalFirstFilledStarComputation
import A12Kernel.Semantics.TemporalTarget

/-! # Direct one-star DateRange `FirstFilledValue` computation -/

namespace A12Kernel

inductive DateRangeFirstFilledComputationElabError where
  | shape (cause : TemporalFirstFilledStarComputationElabError)
  deriving Repr, DecidableEq

/-- One fixed DateRange target and one direct single-level starred source sharing one exact admitted declaration pair. -/
inductive CheckedDateRangeFirstFilledComputation (model : FlatModel) where
  | isoSlash
      (shape : CheckedTemporalFirstFilledStarComputation model .dateRangeIsoSlash)
  | dayMonthYearDash
      (shape : CheckedTemporalFirstFilledStarComputation model .dateRangeDayMonthYearDash)

/-- Check either exact admitted DateRange declaration pair without widening operands, nesting, or document architecture. -/
def checkDateRangeFirstFilledComputation
    (model : FlatModel) (declaringGroup : GroupPath) (targetField : FieldId)
    (authored : SurfaceStarFieldPath) :
    Except DateRangeFirstFilledComputationElabError
      (CheckedDateRangeFirstFilledComputation model) := do
  match checkTemporalFirstFilledStarComputation
      model declaringGroup targetField authored .dateRangeIsoSlash with
  | .ok shape => pure (.isoSlash shape)
  | .error (.targetCarrier _) =>
      let shape ← checkTemporalFirstFilledStarComputation
        model declaringGroup targetField authored .dateRangeDayMonthYearDash
          |>.mapError .shape
      pure (.dayMonthYearDash shape)
  | .error cause => throw (.shape cause)

/-- Project one checked DateRange cell into the typed root result consumed by the target policy. Source stored text is not selected. -/
def dateRangeFirstFilledCellAt
    (addressed : CheckedAddressedCell) : DateRangeComputationResult :=
  match observeCell .computation addressed.cell with
  | .value (.dateRange (.exact range)) => .value range
  | .value (.dateRange _) => .poison .malformed
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

/-- Execute one checked carrier through the single document, bridge the typed range into resolved full-Date endpoints, and render through the retained target policy. -/
private def executeWith
    (shape : CheckedTemporalFirstFilledStarComputation model carrier)
    (format : DateRangeFormat)
    (input : CheckedDocument model) :
    Except DateRangeFirstFilledComputationFault DateRangeTargetOutcome := do
  let resolved ← shape.source.resolveCheckedField input []
    |>.mapError .source
  format.evaluateComputationResult (evalDateRangeFirstFilledCells resolved.cells)
    |>.mapError fun
      | .unresolvedEndpoint range => .unresolvedEndpoint range

/-- Execute through the single checked document and the exact target policy retained during assembly. -/
def execute (operation : CheckedDateRangeFirstFilledComputation model)
    (input : CheckedDocument model) :
    Except DateRangeFirstFilledComputationFault DateRangeTargetOutcome :=
  match operation with
  | .isoSlash shape => executeWith shape .isoSlash input
  | .dayMonthYearDash shape => executeWith shape .dayMonthYearDash input

end CheckedDateRangeFirstFilledComputation

end A12Kernel
