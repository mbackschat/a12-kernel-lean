import A12Kernel.Elaboration.TemporalFirstFilledStarComputation
import A12Kernel.Semantics.FirstFilledValue

/-! # Direct one-star DateFragment `FirstFilledValue` computation -/

namespace A12Kernel

abbrev DateFragmentFirstFilledComputationElabError :=
  TemporalFirstFilledStarComputationElabError

/-- One fixed `MM` DateFragment target and one direct single-level starred source of the same exact represented carrier. -/
abbrev CheckedDateFragmentFirstFilledComputation (model : FlatModel) :=
  CheckedTemporalFirstFilledStarComputation model .monthFragment

/-- Check the exact externally measured DateFragment computation shape. Wider formats, operands, nesting, validation use, and target application remain outside this boundary. -/
def checkDateFragmentFirstFilledComputation
    (model : FlatModel) (declaringGroup : GroupPath) (targetField : FieldId)
    (authored : SurfaceStarFieldPath) :
    Except DateFragmentFirstFilledComputationElabError
      (CheckedDateFragmentFirstFilledComputation model) :=
  checkTemporalFirstFilledStarComputation
    model declaringGroup targetField authored .monthFragment

/-- Project one checked DateFragment cell to the token consumed by the shared first-filled scan. The reviewed row establishes the `MM` output value, not whether the engine copies or renders it. -/
def dateFragmentFirstFilledCellAt
    (addressed : CheckedAddressedCell) : ValueListCell .token :=
  match observeCell .computation addressed.cell, addressed.stored with
  | .value (.temporal (.date _)), some token => .present token
  | .value _, _ => .unknown .malformed
  | .empty, _ => .empty
  | .unknown cause, _ | .poison cause, _ => .unknown cause

namespace CheckedDateFragmentFirstFilledComputation

/-- Execute the checked source over immutable rows and retain only the measured value/clear/poison result boundary. -/
def execute (operation : CheckedDateFragmentFirstFilledComputation model)
    (input : CheckedDocument model) :
    Except CheckedStarDocumentError TokenComputationResult := do
  let resolved ← operation.source.resolveCheckedField input []
  let side : ResolvedValueListSide .token := {
    cells := resolved.cells.map dateFragmentFirstFilledCellAt
    hasUninstantiatedTail := resolved.topology.domain.hasOpenTail
    hasHaving := false
  }
  pure (evalFirstFilledToken side).asComputationResult

end CheckedDateFragmentFirstFilledComputation

end A12Kernel
