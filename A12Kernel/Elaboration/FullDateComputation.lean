import A12Kernel.Elaboration.FullDateComputationApplication
import A12Kernel.Elaboration.TemporalTargetPolicy

/-! # Checked nonrepeatable full-Date field copy

This capsule resolves one ordinary nonrepeatable full-Date source and one distinct full-Date target from the same validated model. Evaluation reads the source once through `CheckedDocument`, preserves computation-phase empty and poison, transports the exact source instant, and delegates rendering and basic checking to `CheckedFullDateTarget`. Alternatives, scheduling, DateTime, partial dates, wider expressions, message construction, and destination compatibility remain separate.
-/

namespace A12Kernel

/-- Static refusal before a direct full-Date field copy can execute. -/
inductive FullDateComputationElabError where
  | target (error : FullDateTargetElabError)
  | source (error : ResolveError)
  | sourceNotTemporal (source : FieldId)
  | sourceKind (source : FieldId) (actual : TemporalKind)
  | sourceComponents (source : FieldId) (actual : TemporalComponents)
  | targetSelfReference (field : FieldId)
  | incoherentCore
  deriving Repr, DecidableEq

/-- Whether one resolved field is exactly an ordinary nonrepeatable full-Date source in this model. -/
def FlatModel.admitsFullDateComputationSource
    (model : FlatModel) (source : FlatTemporalField) : Bool :=
  match model.lookupUniqueId source.id with
  | .error _ => false
  | .ok declaration =>
      declaration.repeatableScope.isEmpty &&
        declaration.toTemporalField? == some source &&
        source.kind == .date &&
        source.components == TemporalComponents.fullDate

/-- One model-certified direct full-Date copy. Source and target identities cannot be substituted after elaboration. -/
structure CheckedFullDateFieldCopy (model : FlatModel) where
  source : FlatTemporalField
  target : CheckedFullDateTarget model
  sourceAdmitted : model.admitsFullDateComputationSource source = true
  targetDistinct : source.id ≠ target.checked.target.id

/-- Resolve one ordinary nonrepeatable full-Date source and one distinct full-Date target against the same validated model. -/
def elaborateFullDateFieldCopy
    (model : FlatModel) (sourceField targetField : FieldId) :
    Except FullDateComputationElabError
      (CheckedFullDateFieldCopy model) := do
  let target ← elaborateFullDateTarget model targetField |>.mapError .target
  let declaration ←
    model.resolveNonrepeatableDeclarationById sourceField |>.mapError .source
  let source ← match declaration.toTemporalField? with
    | some source => pure source
    | none => throw (.sourceNotTemporal sourceField)
  if _hKind : source.kind = .date then
    if _hComponents : source.components = TemporalComponents.fullDate then
      if hDistinct : source.id = target.checked.target.id then
        throw (.targetSelfReference targetField)
      else
        if hSource :
            model.admitsFullDateComputationSource source = true then
          pure {
            source
            target
            sourceAdmitted := hSource
            targetDistinct := hDistinct }
        else
          throw .incoherentCore
    else
      throw (.sourceComponents source.id source.components)
  else
    throw (.sourceKind source.id source.kind)

/-- Structural failure outside the rich full-Date result domain. -/
inductive FullDateComputationFault where
  | document (error : CheckedDocumentError)
  | sourceValueKind (source : FieldId)
  | target (error : FullDateTargetEvaluationFault)
  deriving Repr, DecidableEq

namespace CheckedFullDateFieldCopy

/-- Project one checked source read to the root full-Date computation result. The exact instant is retained; decoded source components and stored text do not become target policy. -/
def readSource (operation : CheckedFullDateFieldCopy model)
    (input : CheckedDocument model) :
    Except FullDateComputationFault FullDateComputationResult :=
  match input.read { field := operation.source.id, path := [] } with
  | .error error => .error (.document error)
  | .ok cell =>
      match observeCell .computation cell with
      | .empty => pure .noValue
      | .poison cause | .unknown cause => pure (.poison cause)
      | .value (.temporal (.date instant _ _)) => pure (.value instant)
      | .value _ => throw (.sourceValueKind operation.source.id)

/-- Execute the checked direct copy through the existing declaration-owned target policy. -/
def evaluateOutcome (operation : CheckedFullDateFieldCopy model)
    (input : CheckedDocument model) :
    Except FullDateComputationFault FullDateTargetOutcome :=
  match operation.readSource input with
  | .error error => .error error
  | .ok result => operation.target.evaluate result |>.mapError .target

/-- Execute and classify the one rich target outcome against the same immutable source document. Residual messages remain already-classified opaque input. -/
def executeResult (operation : CheckedFullDateFieldCopy model)
    (input : CheckedDocument model)
    (residualMessages : List ResidualMessage) :
    Except FullDateComputationFault
      (FullDateComputationRunView ResidualMessage) := do
  let outcome ← operation.evaluateOutcome input
  pure (FullDateComputationRunView.fromOutcomes input residualMessages
    [(operation.target.checked.target.id, outcome)])

end CheckedFullDateFieldCopy

end A12Kernel
