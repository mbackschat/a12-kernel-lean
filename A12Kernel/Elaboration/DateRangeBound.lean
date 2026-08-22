import A12Kernel.Elaboration.CheckedDocument
import A12Kernel.Semantics.DateComparison
import A12Kernel.Semantics.DateNumeric
import A12Kernel.Semantics.DateRangeOverlap

/-! # Checked direct DateRange reads, bound extraction, fixed-Date comparison, and numeric components -/

namespace A12Kernel

/-- Static refusal before one checked direct DateRange can be read. -/
inductive DirectDateRangeElabError where
  | source (error : ResolveError)
  | sourceNotDateRange (source : FieldId) (actual : SurfaceScalarKind)
  | unsupportedPolicy (source : FieldId) (format separator : String)
  | incoherentCore
  deriving Repr, DecidableEq

abbrev DateRangeBoundElabError := DirectDateRangeElabError

/-- Recover the declaration policy and checked input profile for one direct nonrepeatable DateRange source. -/
def FlatModel.directDateRangeInput?
    (model : FlatModel) (source : FlatDateRangeField) :
    Option (DateRangeDeclarationPolicy × DateRangeInputFormat) :=
  match model.lookupUniqueId source.id with
  | .error _ => none
  | .ok declaration =>
      if declaration.repeatableScope.isEmpty then
        match certifyDateRangeInputField declaration with
        | .ok checked =>
            if checked.field == source then some (checked.policy, checked.format)
            else none
        | .error _ => none
      else
        none

/-- One model-certified direct nonrepeatable DateRange field retaining the declaration-owned checked input profile. -/
structure CheckedDirectDateRange (model : FlatModel) where
  private mk ::
  source : FlatDateRangeField
  policy : DateRangeDeclarationPolicy
  format : DateRangeInputFormat
  sourceAdmitted : model.directDateRangeInput? source = some (policy, format)

/-- Whether one checked input profile supplies exact full-Date endpoints under the model's optional Base Year. -/
def DateRangeInputFormat.supportsDirectBound
    (format : DateRangeInputFormat) (baseYear : Option Int) : Bool :=
  match format with
  | .exact _ | .yearFragment | .yearMonthFragment => true
  -- Every yearless presentation needs the model's Base Year to supply the missing
  -- year, and the declared spelling does not change that.
  | .yearlessMonth | .yearlessMonthDay | .yearlessMonthConcatenated
  | .yearlessDayMonthDotted => baseYear.isSome

/-- One selected endpoint of an exact-valued direct DateRange field. -/
structure CheckedDateRangeBound (model : FlatModel)
    extends CheckedDirectDateRange model where
  private mk ::
  bound : DateRangeBound
  sourceSupportsBound :
    toCheckedDirectDateRange.format.supportsDirectBound model.baseYear = true

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

/-- Resolve one direct field and accept every DateRange input profile decoded by `CheckedDocument`. -/
def elaborateDirectDateRange (model : FlatModel) (sourceField : FieldId) :
    Except DirectDateRangeElabError (CheckedDirectDateRange model) := do
  let declaration ←
    model.resolveNonrepeatableDeclarationById sourceField |>.mapError .source
  let checked ← certifyDateRangeInputField declaration |>.mapError fun
    | .notDateRange _ actual =>
        .sourceNotDateRange sourceField actual.surfaceKind
    | .unsupportedPolicy _ format separator =>
        .unsupportedPolicy sourceField format separator
    | .incoherentCore => .incoherentCore
  if hSource : model.directDateRangeInput? checked.field =
      some (checked.policy, checked.format) then
    pure {
      source := checked.field
      policy := checked.policy
      format := checked.format
      sourceAdmitted := hSource }
  else
    throw .incoherentCore

/-- Refine the shared direct source to an exact-valued policy before attaching one selected endpoint. -/
def elaborateDateRangeBound (model : FlatModel) (sourceField : FieldId)
    (bound : DateRangeBound) :
    Except DateRangeBoundElabError (CheckedDateRangeBound model) := do
  let source ← elaborateDirectDateRange model sourceField
  if hSupported : source.format.supportsDirectBound model.baseYear then
    pure {
      toCheckedDirectDateRange := source
      bound
      sourceSupportsBound := hSupported }
  else
    throw (.unsupportedPolicy sourceField source.policy.format source.policy.separator)

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

/-- Structural failure outside one phase-sensitive direct DateRange observation. -/
inductive DirectDateRangeFault where
  | document (error : CheckedDocumentError)
  | sourceValueKind (source : FieldId)
  | sourceValueProfile (source : FieldId) (value : DateRangeCellValue)
  deriving Repr, DecidableEq

abbrev DateRangeBoundFault := DirectDateRangeFault

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

namespace CheckedDirectDateRange

/-- Read one whole range through the sole immutable checked-document route while retaining exact or fragment identity. Empty and formal unavailability retain their phase-specific observation constructors. -/
def evaluate (operation : CheckedDirectDateRange model) (phase : Phase)
    (input : CheckedDocument model) :
    Except DirectDateRangeFault (CellObservation DateRangeCellValue) := do
  let cell ← input.read { field := operation.source.id, path := [] }
    |>.mapError .document
  match observeCell phase cell with
  | .empty => pure .empty
  | .value (.dateRange value) => pure (.value value)
  | .value _ => throw (.sourceValueKind operation.source.id)
  | .unknown cause => pure (.unknown cause)
  | .poison cause => pure (.poison cause)

end CheckedDirectDateRange

namespace CheckedDateRangeBound

/-- Select one endpoint after exact-valued profile refinement and the shared direct DateRange read. Any non-exact runtime carrier still fails defensively if a malformed checked document crosses that static boundary. -/
def evaluate (operation : CheckedDateRangeBound model) (phase : Phase)
    (input : CheckedDocument model) :
    Except DateRangeBoundFault (CellObservation DateValue) := do
  let observed ← operation.toCheckedDirectDateRange.evaluate phase input
  match observed with
  | .empty => pure .empty
  | .value (.exact value) => pure (.value (value.select operation.bound))
  | .value value => throw (.sourceValueProfile operation.source.id value)
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
