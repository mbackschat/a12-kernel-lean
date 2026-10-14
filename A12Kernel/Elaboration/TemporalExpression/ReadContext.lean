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

/-- Public read contexts accept caller scope; global fields stay relevant before every consumer's
cell or extent gate, just as in the common partial preliminary (spec/10 §5). -/
def effectiveScope (context : TemporalPartialReadContext model) : ValidationRelevanceScope :=
  context.scope.withGlobals model

def readCell (context : TemporalPartialReadContext model) (row : Env) (field : FieldId) :
    Except ScalarTemporalEvaluationFault (Option CheckedCell) := do
  discard <| context.document.cellAddress row field |>.mapError .addressing
  if !context.effectiveScope.coversField model field row then return none
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
  match ← source.readPartialDocumentCell context.document context.scope outer context.read |>.mapError .addressing with
  | none => pure none
  | some .empty => pure (some .empty)
  | some (.unknown cause) => pure (some (.unknown cause))
  | some (.poison cause) => pure (some (.poison cause))
  | some (.value (row, cell)) =>
      pure (some (.value (cell, ← context.storedText row source.targetDeclaration.id cell)))

end TemporalPartialReadContext

/-- Evaluates a filtered shift amount at the row the caller's context binds. Only a route holding
the checked document can supply it; the default refuses with a structural fault. A consumer that maps
structural faults to unavailability still turns that refusal into UNKNOWN, so such routes must stay
behind the `requiresAddressed` gate. -/
abbrev FilteredShiftAmountReader (model : FlatModel) :=
  CheckedFilteredShiftAmount model →
    Except ScalarTemporalEvaluationFault (Except NumericValidationUnavailable NumericArithmeticOutcome)

def FilteredShiftAmountReader.unavailable : FilteredShiftAmountReader model :=
  fun _ => throw (.addressing (.checkedDocumentRequired []))
end A12Kernel
