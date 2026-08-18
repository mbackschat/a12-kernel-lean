import A12Kernel.Elaboration.TemporalFirstFilledStarComputation
import A12Kernel.Elaboration.TemporalTargetPolicy

/-! # Direct one-star full-Date `FirstFilledValue` computation -/

namespace A12Kernel

inductive FullDateFirstFilledComputationElabError where
  | shape (cause : TemporalFirstFilledStarComputationElabError)
  | targetPolicy (cause : FullDateTargetElabError)
  deriving Repr, DecidableEq

/-- Carrier-specific direct-star shape retained beneath the checked full-Date computation boundary. -/
inductive FullDateFirstFilledShape (model : FlatModel) where
  | iso
      (shape : CheckedTemporalFirstFilledStarComputation model .fullDateIso)
  | dotted
      (shape : CheckedTemporalFirstFilledStarComputation model .fullDateDotted)

/-- One fixed full-Date target and one direct single-level starred source sharing one exact admitted declaration format. The private constructor keeps the separately checked target policy tied to the assembly route. -/
structure CheckedFullDateFirstFilledComputation (model : FlatModel) where
  private mk ::
  shape : FullDateFirstFilledShape model
  targetPolicy : CheckedFullDateTarget model

/-- Check the two exact bounded full-Date formats. The ISO composition is externally measured; dotted target rendering is measured separately while its direct `FirstFilledValue` composition remains pending. Wider formats, policies, operands, nesting, validation use, and application stay outside. -/
def checkFullDateFirstFilledComputation
    (model : FlatModel) (declaringGroup : GroupPath) (targetField : FieldId)
    (authored : SurfaceStarFieldPath) :
    Except FullDateFirstFilledComputationElabError
      (CheckedFullDateFirstFilledComputation model) := do
  match checkTemporalFirstFilledStarComputation
      model declaringGroup targetField authored .fullDateIso with
  | .ok shape =>
      let targetPolicy ← elaborateFullDateTarget model targetField
        |>.mapError .targetPolicy
      pure { shape := .iso shape, targetPolicy }
  | .error (.targetCarrier _) =>
      let shape ← checkTemporalFirstFilledStarComputation
        model declaringGroup targetField authored .fullDateDotted
          |>.mapError .shape
      let targetPolicy ← elaborateFullDateTarget model targetField
        |>.mapError .targetPolicy
      pure { shape := .dotted shape, targetPolicy }
  | .error cause => throw (.shape cause)

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

/-- Execute one checked carrier over immutable rows, then let the existing target policy render and classify the selected typed Date. -/
private def executeWith
    (shape : CheckedTemporalFirstFilledStarComputation model carrier)
    (targetPolicy : CheckedFullDateTarget model)
    (input : CheckedDocument model) :
    Except FullDateFirstFilledComputationFault FullDateTargetOutcome := do
  let resolved ← shape.source.resolveCheckedField input []
    |>.mapError .source
  targetPolicy.evaluate (evalFullDateFirstFilledCells resolved.cells)
    |>.mapError .target

/-- Execute through the single checked document and the exact full-Date target policy retained during assembly. -/
def execute (operation : CheckedFullDateFirstFilledComputation model)
    (input : CheckedDocument model) :
    Except FullDateFirstFilledComputationFault FullDateTargetOutcome :=
  match operation with
  | { shape := .iso shape, targetPolicy } =>
      executeWith shape targetPolicy input
  | { shape := .dotted shape, targetPolicy } =>
      executeWith shape targetPolicy input

end CheckedFullDateFirstFilledComputation

end A12Kernel
