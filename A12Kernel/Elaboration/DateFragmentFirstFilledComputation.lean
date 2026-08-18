import A12Kernel.Elaboration.TemporalFirstFilledStarComputation
import A12Kernel.Semantics.FirstFilledValue

/-! # Direct one-star DateFragment `FirstFilledValue` computation -/

namespace A12Kernel

abbrev DateFragmentFirstFilledComputationElabError :=
  TemporalFirstFilledStarComputationElabError

/-- One fixed DateFragment target and one direct single-level starred source sharing one exact admitted declaration format. -/
inductive CheckedDateFragmentFirstFilledComputation (model : FlatModel) where
  | month
      (shape : CheckedTemporalFirstFilledStarComputation model .monthFragment)
  | year
      (shape : CheckedTemporalFirstFilledStarComputation model .yearFragment)
  | yearMonth
      (shape :
        CheckedTemporalFirstFilledStarComputation model .yearMonthFragment)
  | monthDay
      (shape :
        CheckedTemporalFirstFilledStarComputation model .monthDayFragment)

/-- Check the four exact admitted DateFragment formats. Direct runtime calibration remains exact only for `MM`; wider operands, nesting, validation use, and target application stay outside. -/
def checkDateFragmentFirstFilledComputation
    (model : FlatModel) (declaringGroup : GroupPath) (targetField : FieldId)
    (authored : SurfaceStarFieldPath) :
    Except DateFragmentFirstFilledComputationElabError
      (CheckedDateFragmentFirstFilledComputation model) :=
  match checkTemporalFirstFilledStarComputation
      model declaringGroup targetField authored .monthFragment with
  | .ok shape => pure (.month shape)
  | .error (.targetCarrier _) =>
      match checkTemporalFirstFilledStarComputation
          model declaringGroup targetField authored .yearFragment with
      | .ok shape => pure (.year shape)
      | .error (.targetCarrier _) =>
          match checkTemporalFirstFilledStarComputation model declaringGroup
              targetField authored .yearMonthFragment with
          | .ok shape => pure (.yearMonth shape)
          | .error (.targetCarrier _) => do
              let shape ← checkTemporalFirstFilledStarComputation model
                declaringGroup targetField authored .monthDayFragment
              pure (.monthDay shape)
          | .error cause => throw cause
      | .error cause => throw cause
  | .error cause => throw cause

/-- Project one checked DateFragment cell to the token consumed by the shared first-filled scan. Only the `MM` runtime row is externally calibrated, and it does not distinguish copy from render. -/
def dateFragmentFirstFilledCellAt
    (addressed : CheckedAddressedCell) : ValueListCell .token :=
  match observeCell .computation addressed.cell, addressed.stored with
  | .value (.temporal (.date _)), some token => .present token
  | .value _, _ => .unknown .malformed
  | .empty, _ => .empty
  | .unknown cause, _ | .poison cause, _ => .unknown cause

namespace CheckedDateFragmentFirstFilledComputation

/-- Execute one checked source over immutable rows and retain only the value/clear/poison token boundary. -/
private def executeWith
    (shape : CheckedTemporalFirstFilledStarComputation model carrier)
    (input : CheckedDocument model) :
    Except CheckedStarDocumentError TokenComputationResult := do
  let resolved ← shape.source.resolveCheckedField input []
  let side : ResolvedValueListSide .token := {
    cells := resolved.cells.map dateFragmentFirstFilledCellAt
    hasUninstantiatedTail := resolved.topology.domain.hasOpenTail
    hasHaving := false
  }
  pure (evalFirstFilledToken side).asComputationResult

/-- Execute every admitted DateFragment policy through the same checked document and exact-token scan. -/
def execute (operation : CheckedDateFragmentFirstFilledComputation model)
    (input : CheckedDocument model) :
    Except CheckedStarDocumentError TokenComputationResult :=
  match operation with
  | .month shape => executeWith shape input
  | .year shape => executeWith shape input
  | .yearMonth shape => executeWith shape input
  | .monthDay shape => executeWith shape input

end CheckedDateFragmentFirstFilledComputation

end A12Kernel
