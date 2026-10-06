import A12Kernel.Elaboration.TemporalExpression.Types
import A12Kernel.Elaboration.PartialSemanticIndex

namespace A12Kernel

/-- Partial availability is independent of a checked cell's omission and formal findings
(spec/10 §5). Index identity remains owned by the scope-prepared preliminary. -/
structure TemporalPartialReadContext (model : FlatModel) where
  document : CheckedDocument model
  scope : ValidationRelevanceScope
  read : Env → FieldId → Except CheckedAddressingError (Option CheckedCell)

namespace TemporalPartialReadContext

def readCell (context : TemporalPartialReadContext model) (row : Env) (field : FieldId) :
    Except ScalarTemporalEvaluationFault (Option CheckedCell) := do
  discard <| context.document.cellAddress row field |>.mapError .addressing
  if !context.scope.coversField model field row then return none
  context.read row field |>.mapError .addressing

def storedText (context : TemporalPartialReadContext model) (row : Env) (field : FieldId)
    (cell : CheckedCell) : Except ScalarTemporalEvaluationFault (Option String) := do
  let address ← context.document.cellAddress row field |>.mapError .addressing
  pure (context.document.storedTextForCell address cell)

/-- Constructors retain their declaration classifier and exact text at the selected coordinate;
an absent selection is empty only under the selector's wildcard target-extent judgment (spec/08 §4). -/
def selectedCell (context : TemporalPartialReadContext model)
    (source : CheckedSemanticIndexSource model) (outer : Env) :
    Except ScalarTemporalEvaluationFault (Option (CellObservation (CheckedCell × Option String))) := do
  let view ← context.document.applyPartialGeneratedPreliminaryForScope context.scope
    |>.mapError (ScalarTemporalEvaluationFault.addressing ∘ CheckedAddressingError.indexPreliminary)
  match ← source.selectPartial view outer context.read |>.mapError .addressing with
  | none => pure none
  | some .empty => pure (if context.scope.coversValueListExtent model source.targetDeclaration.path
      source.indexDeclaration.repeatableScope.dropLast [source.group.level] outer then some .empty else none)
  | some (.unknown cause) => pure (some (.unknown cause))
  | some (.poison cause) => pure (some (.poison cause))
  | some (.value row) =>
      match ← context.readCell row source.targetDeclaration.id with
      | none => pure none
      | some cell => pure (some (.value (cell, ← context.storedText row source.targetDeclaration.id cell)))

end TemporalPartialReadContext
end A12Kernel
