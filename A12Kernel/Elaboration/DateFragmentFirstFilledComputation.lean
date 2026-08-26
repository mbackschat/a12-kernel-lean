import A12Kernel.Elaboration.TemporalFirstFilledStarComputation
import A12Kernel.Elaboration.ExactTokenComputationResult
import A12Kernel.Elaboration.StringComputationRunApplication
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

/-- Check the four exact admitted DateFragment formats. Direct runtime calibration remains exact only for `MM`; wider operands, nesting, and validation use stay outside. -/
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

/-- The exact fixed target retained by any admitted DateFragment carrier. -/
def CheckedDateFragmentFirstFilledComputation.targetField :
    CheckedDateFragmentFirstFilledComputation model → FieldId
  | .month shape => shape.target.id
  | .year shape => shape.target.id
  | .yearMonth shape => shape.target.id
  | .monthDay shape => shape.target.id

/-- One checked DateFragment `FirstFilledValue` result backed by the common exact-text channels. Retaining the operation ties every action to the exact admitted fragment target and declaration profile. -/
structure DateFragmentFirstFilledComputationRunView (model : FlatModel)
    (ResidualMessage : Type) where
  private mk ::
  operation : CheckedDateFragmentFirstFilledComputation model
  string : StringComputationRunView ResidualMessage

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

/-- Execute one checked DateFragment selection and classify its exact stored token relative to the immutable source target. This internal result boundary does not claim that the Kernel copies rather than rerenders the selected fragment. -/
def executeResult (operation : CheckedDateFragmentFirstFilledComputation model)
    (input : CheckedDocument model)
    (residualMessages : List ResidualMessage) :
    Except CheckedStarDocumentError
      (DateFragmentFirstFilledComputationRunView model ResidualMessage) := do
  let result ← operation.execute input
  let targetField := operation.targetField
  let string := StringComputationRunView.fromSourcedOutcomes residualMessages [{
    targetField
    outcome := result.asExactStringTargetOutcome
    source := input.sourceStringTargetState targetField
  }]
  pure { operation, string }

end CheckedDateFragmentFirstFilledComputation

namespace DateFragmentFirstFilledComputationRunView

/-- Apply retained source-relative fragment actions to a separately supplied checked document of the same model. The result is an exact root text-state projection, not a reconstructed document or implicit validation pass. -/
def applyToChecked
    (view : DateFragmentFirstFilledComputationRunView model ResidualMessage)
    (destination : CheckedDocument model) :
    Except (StringComputationRunView.StringComputationRunApplicationError FieldId)
      (StringComputationDestination FieldId) :=
  view.string.applyTo destination.sourceStringTargetState

end DateFragmentFirstFilledComputationRunView

end A12Kernel
