import A12Kernel.Elaboration.TemporalFirstFilledStarComputation
import A12Kernel.Elaboration.DateRangeTargetPresentation
import A12Kernel.Semantics.TemporalTarget

/-! # Direct one-star DateRange `FirstFilledValue` computation -/

namespace A12Kernel

inductive DateRangeFirstFilledComputationElabError where
  | shape (cause : TemporalFirstFilledStarComputationElabError)
  deriving Repr, DecidableEq

/-- One fixed DateRange target and one direct single-level starred source sharing one admitted declaration profile. -/
inductive CheckedDateRangeFirstFilledComputation (model : FlatModel) where
  | isoSlash
      (shape : CheckedTemporalFirstFilledStarComputation model .dateRangeIsoSlash)
  | dayMonthYearDash
      (shape : CheckedTemporalFirstFilledStarComputation model .dateRangeDayMonthYearDash)
  | yearFragment
      (shape : CheckedTemporalFirstFilledStarComputation model .dateRangeYearFragment)
  | yearMonthFragment
      (shape : CheckedTemporalFirstFilledStarComputation model .dateRangeYearMonthFragment)
  | monthFragment
      (shape : CheckedTemporalFirstFilledStarComputation model .dateRangeMonthFragment)
  | monthDayFragment
      (shape : CheckedTemporalFirstFilledStarComputation model .dateRangeMonthDayFragment)

/-- Check one of the six admitted matching DateRange declaration profiles without widening operands, nesting, or document architecture. -/
def checkDateRangeFirstFilledComputation
    (model : FlatModel) (declaringGroup : GroupPath) (targetField : FieldId)
    (authored : SurfaceStarFieldPath) :
    Except DateRangeFirstFilledComputationElabError
      (CheckedDateRangeFirstFilledComputation model) := do
  match checkTemporalFirstFilledStarComputation
      model declaringGroup targetField authored .dateRangeIsoSlash with
  | .ok shape => pure (.isoSlash shape)
  | .error (.targetCarrier _) =>
      match checkTemporalFirstFilledStarComputation
          model declaringGroup targetField authored .dateRangeDayMonthYearDash with
      | .ok shape => pure (.dayMonthYearDash shape)
      | .error (.targetCarrier _) =>
          match checkTemporalFirstFilledStarComputation
              model declaringGroup targetField authored .dateRangeYearFragment with
          | .ok shape => pure (.yearFragment shape)
          | .error (.targetCarrier _) =>
              match checkTemporalFirstFilledStarComputation model declaringGroup
                  targetField authored .dateRangeYearMonthFragment with
              | .ok shape => pure (.yearMonthFragment shape)
              | .error (.targetCarrier _) =>
                  match checkTemporalFirstFilledStarComputation model declaringGroup
                      targetField authored .dateRangeMonthFragment with
                  | .ok shape => pure (.monthFragment shape)
                  | .error (.targetCarrier _) =>
                      let shape ← checkTemporalFirstFilledStarComputation
                        model declaringGroup targetField authored
                          .dateRangeMonthDayFragment |>.mapError .shape
                      pure (.monthDayFragment shape)
                  | .error cause => throw (.shape cause)
              | .error cause => throw (.shape cause)
          | .error cause => throw (.shape cause)
      | .error cause => throw (.shape cause)
  | .error cause => throw (.shape cause)

/-- Root result retaining exact or yearless DateRange cell identity until the checked target policy consumes it. -/
inductive DateRangeFirstFilledResult where
  | noValue
  | value (range : DateRangeCellValue)
  | poison (cause : FormalCause)
  deriving Repr, DecidableEq

/-- Project one checked DateRange cell into the typed root result consumed by the target policy. Source stored text is not selected. -/
def dateRangeFirstFilledCellAt
    (addressed : CheckedAddressedCell) : DateRangeFirstFilledResult :=
  match observeCell .computation addressed.cell with
  | .value (.dateRange range) => .value range
  | .value _ => .poison .malformed
  | .empty => .noValue
  | .unknown cause | .poison cause => .poison cause

/-- Select the first present DateRange or reached formal cause; exhaustion keeps the no-value identity. -/
def evalDateRangeFirstFilledCells :
    List CheckedAddressedCell → DateRangeFirstFilledResult
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

/-- Consume a selected exact or yearless cell through its matching checked declaration profile. -/
private def evaluateResult (format : DateRangeInputFormat) :
    DateRangeFirstFilledResult →
      Except DateRangeFirstFilledComputationFault DateRangeTargetOutcome
  | .noValue => .ok .noValue
  | .poison cause => .ok (.poison cause)
  | .value (.exact range) =>
      format.evaluateExactValue range |>.mapError fun
        | .unresolvedEndpoint value => .unresolvedEndpoint value
  | .value (.yearlessMonth start finish) =>
      match format with
      | .yearlessMonth => .ok (.accepted
          (DateRangeInputFormat.renderYearlessMonth start finish))
      | _ => .ok (.poison .malformed)
  | .value (.yearlessMonthDay start finish) =>
      match format with
      | .yearlessMonthDay => .ok (.accepted
          (DateRangeInputFormat.renderYearlessMonthDay start finish))
      | _ => .ok (.poison .malformed)

/-- Execute one checked carrier through the single document and render its exact or yearless cell through the retained target policy. -/
private def executeWith
    (shape : CheckedTemporalFirstFilledStarComputation model carrier)
    (format : DateRangeInputFormat)
    (input : CheckedDocument model) :
    Except DateRangeFirstFilledComputationFault DateRangeTargetOutcome := do
  let resolved ← shape.source.resolveCheckedField input []
    |>.mapError .source
  evaluateResult format (evalDateRangeFirstFilledCells resolved.cells)

/-- Execute through the single checked document and the target policy retained during assembly. -/
def execute (operation : CheckedDateRangeFirstFilledComputation model)
    (input : CheckedDocument model) :
    Except DateRangeFirstFilledComputationFault DateRangeTargetOutcome :=
  match operation with
  | .isoSlash shape => executeWith shape (.exact .isoSlash) input
  | .dayMonthYearDash shape => executeWith shape (.exact .dayMonthYearDash) input
  | .yearFragment shape => executeWith shape .yearFragment input
  | .yearMonthFragment shape => executeWith shape .yearMonthFragment input
  | .monthFragment shape => executeWith shape .yearlessMonth input
  | .monthDayFragment shape => executeWith shape .yearlessMonthDay input

end CheckedDateRangeFirstFilledComputation

end A12Kernel
