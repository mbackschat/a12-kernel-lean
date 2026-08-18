import A12Kernel.Elaboration.CheckedDocument
import A12Kernel.Semantics.DateComparison
import A12Kernel.Semantics.DateNumeric
import A12Kernel.Semantics.DateRangeOverlap

/-! # Checked direct DateRange bound extraction, fixed-Date comparison, and numeric components -/

namespace A12Kernel

/-- Static refusal before one bounded direct DateRange endpoint can be read. -/
inductive DateRangeBoundElabError where
  | source (error : ResolveError)
  | sourceNotDateRange (source : FieldId) (actual : SurfaceScalarKind)
  | unsupportedPolicy (source : FieldId) (format separator : String)
  | incoherentCore
  deriving Repr, DecidableEq

/-- Whether one resolved field is exactly a nonrepeatable DateRange source under a canonically supported stored-input policy. -/
def FlatModel.admitsDateRangeBoundSource
    (model : FlatModel) (source : FlatDateRangeField) : Bool :=
  match model.lookupUniqueId source.id with
  | .error _ => false
  | .ok declaration =>
      declaration.repeatableScope.isEmpty &&
        declaration.toDateRangeField? == some source &&
        match declaration.toDateRangeDeclarationPolicy? with
        | some policy => (DateRangeFormat.ofPolicy? policy).isSome
        | none => false

/-- One selected endpoint of a model-certified direct nonrepeatable DateRange field. -/
structure CheckedDateRangeBound (model : FlatModel) where
  private mk ::
  source : FlatDateRangeField
  bound : DateRangeBound
  sourceAdmitted : model.admitsDateRangeBoundSource source = true

/-- Authored side occupied by the selected DateRange bound in one full-Date comparison. -/
inductive DateRangeBoundComparisonPosition where
  | left
  | right
  deriving Repr, DecidableEq

/-- One checked direct DateRange bound composed with the existing full-Date comparison consumer. -/
structure CheckedDateRangeBoundComparison (model : FlatModel)
    extends CheckedDateRangeBound model where
  position : DateRangeBoundComparisonPosition
  comparison : TemporalComparisonOp
  expected : FullDate

/-- One checked direct DateRange bound composed with the existing typed Date-component consumer. -/
structure CheckedDateRangeBoundComponent (model : FlatModel)
    extends CheckedDateRangeBound model where
  part : DateNumericPart

/-- Resolve one direct field and accept only the two DateRange policies whose stored input is decoded by `CheckedDocument`. -/
def elaborateDateRangeBound (model : FlatModel) (sourceField : FieldId)
    (bound : DateRangeBound) :
    Except DateRangeBoundElabError (CheckedDateRangeBound model) := do
  let declaration ←
    model.resolveNonrepeatableDeclarationById sourceField |>.mapError .source
  let source ← match declaration.toDateRangeField? with
    | some source => pure source
    | none => throw (.sourceNotDateRange sourceField
        declaration.policy.kind.surfaceKind)
  let policy ← match declaration.toDateRangeDeclarationPolicy? with
    | some policy => pure policy
    | none => throw .incoherentCore
  match DateRangeFormat.ofPolicy? policy with
  | none => throw (.unsupportedPolicy sourceField policy.format policy.separator)
  | some _ =>
      if hSource : model.admitsDateRangeBoundSource source = true then
        pure { source, bound, sourceAdmitted := hSource }
      else
        throw .incoherentCore

/-- Resolve one direct bound and retain its authored comparison position and fixed full-Date peer. -/
def elaborateDateRangeBoundComparison (model : FlatModel)
    (sourceField : FieldId) (bound : DateRangeBound)
    (position : DateRangeBoundComparisonPosition)
    (comparison : TemporalComparisonOp) (expected : FullDate) :
    Except DateRangeBoundElabError (CheckedDateRangeBoundComparison model) := do
  let source ← elaborateDateRangeBound model sourceField bound
  pure { source with position, comparison, expected }

/-- Resolve one direct bound and retain the selected numeric Date component. -/
def elaborateDateRangeBoundComponent (model : FlatModel)
    (sourceField : FieldId) (bound : DateRangeBound)
    (part : DateNumericPart) :
    Except DateRangeBoundElabError (CheckedDateRangeBoundComponent model) := do
  let source ← elaborateDateRangeBound model sourceField bound
  pure { source with part }

/-- Structural failure outside the phase-sensitive endpoint observation. -/
inductive DateRangeBoundFault where
  | document (error : CheckedDocumentError)
  | sourceValueKind (source : FieldId)
  deriving Repr, DecidableEq

/-- Defensive failure while composing one selected endpoint with a full-Date comparison. -/
inductive DateRangeBoundComparisonFault where
  | bound (cause : DateRangeBoundFault)
  | selectedDateUnavailable (source : FieldId) (value : DateValue)
  deriving Repr, DecidableEq

/-- One-read result for Execute and Explain: exact selected observation plus its existing comparison verdict. -/
structure DateRangeBoundComparisonResult where
  selected : CellObservation DateValue
  verdict : Verdict
  deriving Repr, DecidableEq

/-- One-read result retaining the exact selected observation beside its established numeric component. -/
structure DateRangeBoundComponentResult where
  selected : CellObservation DateValue
  component : NumericOperand
  deriving Repr, DecidableEq

namespace CheckedDateRangeBound

/-- Read one selected endpoint through the sole immutable checked-document route. Empty and exact formal unavailability retain their phase-specific observation constructors. -/
def evaluate (operation : CheckedDateRangeBound model) (phase : Phase)
    (input : CheckedDocument model) :
    Except DateRangeBoundFault (CellObservation DateValue) := do
  let cell ← input.read { field := operation.source.id, path := [] }
    |>.mapError .document
  match observeCell phase cell with
  | .empty => pure .empty
  | .value (.dateRange value) => pure (.value (value.select operation.bound))
  | .value _ => throw (.sourceValueKind operation.source.id)
  | .unknown cause => pure (.unknown cause)
  | .poison cause => pure (.poison cause)

end CheckedDateRangeBound

namespace CheckedDateRangeBoundComparison

/-- Project an exact selected endpoint into the established full-Date comparison domain while keeping impossible malformed payloads explicit. -/
def projectSelected (source : FieldId) :
    CellObservation DateValue →
    Except DateRangeBoundComparisonFault (CellObservation FullDate)
  | .empty => .ok .empty
  | .value value =>
      match value.toFullDate? with
      | some date => .ok (.value date)
      | none => throw (.selectedDateUnavailable source value)
  | .unknown cause => .ok (.unknown cause)
  | .poison cause => .ok (.poison cause)

/-- Compare one already-selected exact endpoint while retaining it for explanation. -/
def evaluateSelected (operation : CheckedDateRangeBoundComparison model)
    (selected : CellObservation DateValue) :
    Except DateRangeBoundComparisonFault DateRangeBoundComparisonResult := do
  let projected ← projectSelected operation.source.id selected
  let expected : CellObservation FullDate := .value operation.expected
  let verdict := match operation.position with
    | .left => operation.comparison.evalObserved projected expected
    | .right => operation.comparison.evalObserved expected projected
  .ok { selected, verdict }

/-- Read the certified source once in validation phase, then delegate its selected endpoint to the established full-Date comparison. -/
def evaluate (operation : CheckedDateRangeBoundComparison model)
    (input : CheckedDocument model) :
    Except DateRangeBoundComparisonFault DateRangeBoundComparisonResult := do
  let selected ←
    (operation.toCheckedDateRangeBound.evaluate .validation input).mapError .bound
  operation.evaluateSelected selected

end CheckedDateRangeBoundComparison

namespace CheckedDateRangeBoundComponent

/-- Project one already-selected exact endpoint through the established typed Date-component semantics. -/
def evaluateSelected (operation : CheckedDateRangeBoundComponent model)
    (selected : CellObservation DateValue) : DateRangeBoundComponentResult := {
  selected
  component := operation.part.fromObservation (·.parts) selected
}

/-- Read the certified source once in validation phase, then project the selected endpoint's numeric Date component. -/
def evaluate (operation : CheckedDateRangeBoundComponent model)
    (input : CheckedDocument model) :
    Except DateRangeBoundFault DateRangeBoundComponentResult := do
  let selected ← operation.toCheckedDateRangeBound.evaluate .validation input
  pure (operation.evaluateSelected selected)

end CheckedDateRangeBoundComponent

end A12Kernel
