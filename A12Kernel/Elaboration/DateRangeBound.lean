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

/-- The one gate this owner reports to a rule author. An unstarred repeatable source read from a
non-iterating rule locus is the shared missing-wildcard class, and it is raised here rather than at
each carrier, so every DateRange endpoint and stored-value carrier reports it identically. The
remaining refusals are kind and declaration-policy classes whose codes belong to their consuming
operator. -/
def DirectDateRangeElabError.diagnostic? :
    DirectDateRangeElabError → Option KernelStaticDiagnostic
  | .source error => error.diagnostic?
  | .sourceNotDateRange _ _ | .unsupportedPolicy _ _ _ | .incoherentCore => none

abbrev DateRangeBoundElabError := DirectDateRangeElabError

/-- Recover the owning declaration, its policy, and its checked input profile for one DateRange
source read at a context that binds the repeatable levels in `scope`. This is the sole admission
projection for the family: the direct nonrepeatable read is its `[]` instance, so a scalar and an
iterated carrier cannot disagree about a declaration's profile. -/
def FlatModel.dateRangeSourceBoundBy
    (model : FlatModel) (scope : List RepeatableLevel)
    (source : FlatDateRangeField) :
    Option (FlatFieldDecl × DateRangeDeclarationPolicy × DateRangeInputFormat) :=
  match model.lookupUniqueId source.id with
  | .error _ => none
  | .ok declaration =>
      if declaration.repetitionBoundBy scope then
        match certifyDateRangeInputField declaration with
        | .ok checked =>
            if checked.field == source then
              some (declaration, checked.policy, checked.format)
            else none
        | .error _ => none
      else
        none

/-- One model-certified DateRange field read at a context that binds the repeatable levels in
`scope`, retaining the declaration-owned checked input profile and the declaration itself. The scope
is data rather than a type index because the condition leaf that carries this certificate is indexed
by its model alone; the scalar refinement below fixes it to `[]`. -/
structure CheckedDateRangeSource (model : FlatModel) where
  private mk ::
  scope : List RepeatableLevel
  source : FlatDateRangeField
  declaration : FlatFieldDecl
  policy : DateRangeDeclarationPolicy
  format : DateRangeInputFormat
  sourceAdmitted :
    model.dateRangeSourceBoundBy scope source =
      some (declaration, policy, format)

/-- One direct nonrepeatable DateRange field: the same certificate at the empty reading scope. A
scalar carrier therefore coerces into the general one, so an iterated consumer accepts a scalar
operand without a second certificate. -/
structure CheckedDirectDateRange (model : FlatModel)
    extends CheckedDateRangeSource model where
  private mk ::
  /-- The refinement is stated about the *declaration* rather than the reading scope, because that
  is the fact a root-reading consumer needs: a declaration crossing no repeatable level addresses
  identically at every environment. -/
  scalarSource : toCheckedDateRangeSource.declaration.repeatableScope = []

/-- Resolve one DateRange operand for a rule iterating `scope`. An operand crossing a level the
locus does not bind is reported as a repeatable reference, which is the class the Kernel reports as
its missing-wildcard refusal. -/
def elaborateDateRangeSourceIn (model : FlatModel)
    (scope : List RepeatableLevel) (sourceField : FieldId) :
    Except DirectDateRangeElabError (CheckedDateRangeSource model) := do
  let resolved ← model.lookupUniqueId sourceField |>.mapError .source
  let declaration ← resolved.requireRepetitionBoundBy scope |>.mapError .source
  let checked ← certifyDateRangeInputField declaration |>.mapError fun
    | .notDateRange _ actual =>
        .sourceNotDateRange sourceField actual.surfaceKind
    | .unsupportedPolicy _ format separator =>
        .unsupportedPolicy sourceField format separator
    | .incoherentCore => .incoherentCore
  if hSource : model.dateRangeSourceBoundBy scope checked.field =
      some (declaration, checked.policy, checked.format) then
    pure {
      scope
      source := checked.field
      declaration
      policy := checked.policy
      format := checked.format
      sourceAdmitted := hSource }
  else
    throw .incoherentCore

/-- Whether one checked input profile supplies exact full-Date endpoints under the model's optional Base Year. -/
def DateRangeInputFormat.supportsDirectBound
    (format : DateRangeInputFormat) (baseYear : Option Int) : Bool :=
  match format with
  | .exact _ | .yearFragment | .yearMonthFragment => true
  -- Every yearless presentation needs the model's Base Year to supply the missing
  -- year, and the declared spelling does not change that.
  | .yearlessMonth | .yearlessMonthDay | .yearlessMonthConcatenated
  | .yearlessDayMonthDotted => baseYear.isSome

/-- One selected endpoint of a DateRange field read at a rule's iterating row. The exact-value gate
is the scalar carrier's, so an unconfigured yearless profile is excluded here exactly as it is
there; the iterated yearless endpoint is a separate unmodelled shape. -/
structure CheckedDateRangeSourceBound (model : FlatModel)
    extends CheckedDateRangeSource model where
  private mk ::
  bound : DateRangeBound
  sourceSupportsBound :
    toCheckedDateRangeSource.format.supportsDirectBound model.baseYear = true

/-- Resolve one endpoint for a rule iterating `scope`, refusing the same profiles the scalar
endpoint owner refuses. -/
def elaborateDateRangeBoundIn (model : FlatModel)
    (scope : List RepeatableLevel) (sourceField : FieldId)
    (bound : DateRangeBound) :
    Except DateRangeBoundElabError (CheckedDateRangeSourceBound model) := do
  let source ← elaborateDateRangeSourceIn model scope sourceField
  if hSupported : source.format.supportsDirectBound model.baseYear then
    pure {
      toCheckedDateRangeSource := source
      bound
      sourceSupportsBound := hSupported }
  else
    throw (.unsupportedPolicy sourceField source.policy.format
      source.policy.separator)

/-- One selected endpoint of an exact-valued DateRange field read at the document root: the general
endpoint below refined by its declaration crossing no repeatable level. -/
structure CheckedDateRangeBound (model : FlatModel)
    extends CheckedDateRangeSourceBound model where
  private mk ::
  scalarSource :
    toCheckedDateRangeSourceBound.declaration.repeatableScope = []


/-- Whether one DateRange declaration is a nonrepeatable source addressable by a scalar consumer at
any locus. Shared by the scalar validation and computation operand surfaces. -/
def FlatModel.nonrepeatableDateRangeSource (model : FlatModel)
    (field : FlatDateRangeField) : Bool :=
  match model.lookupUniqueId field.id with
  | .ok declaration =>
      declaration.repeatableScope.isEmpty &&
        declaration.policy.kind.surfaceKind == .dateRange
  | .error _ => false

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

/-- Resolve one direct field and accept every DateRange input profile decoded by `CheckedDocument`.
This is the general resolver at the empty scope, so a repeatable declaration is refused with the same
class it draws at any other unbound level. -/
def elaborateDirectDateRange (model : FlatModel) (sourceField : FieldId) :
    Except DirectDateRangeElabError (CheckedDirectDateRange model) := do
  let checked ← elaborateDateRangeSourceIn model [] sourceField
  -- The empty scope admits only a nonrepeatable declaration, so this reconstruction keeps the
  -- refinement decidable without a law about the resolver.
  if hScalar : checked.declaration.repeatableScope = [] then
    pure { toCheckedDateRangeSource := checked, scalarSource := hScalar }
  else
    throw .incoherentCore

/-- Refine the shared direct source to an exact-valued policy before attaching one selected endpoint. -/
def elaborateDateRangeBound (model : FlatModel) (sourceField : FieldId)
    (bound : DateRangeBound) :
    Except DateRangeBoundElabError (CheckedDateRangeBound model) := do
  let source ← elaborateDateRangeBoundIn model [] sourceField bound
  -- The empty scope admits only a nonrepeatable declaration, so this reconstruction keeps the
  -- refinement decidable without a law about the resolver.
  if hScalar : source.declaration.repeatableScope = [] then
    pure { toCheckedDateRangeSourceBound := source, scalarSource := hScalar }
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

/-- Structural failure outside one phase-sensitive direct DateRange observation. -/
inductive DirectDateRangeFault where
  | document (error : CheckedDocumentError)
  /-- The reading environment did not bind a level the source's declaration crosses. Reachable only
  for a source read at a row, and never for one read at the document root. -/
  | environment (error : EnvBindingError)
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

namespace CheckedDateRangeSource

/-- Project one already-observed cell into the retained exact-or-fragment range identity. Every read
route shares this, so none can disagree about emptiness, kind, or formal unavailability — only about
which cell it reaches. A keyed lookup supplies its observation directly, which is why the projection
is separate from the cell read below. -/
def projectRange (source : FieldId) :
    CellObservation → Except DirectDateRangeFault (CellObservation DateRangeCellValue)
  | .empty => .ok .empty
  | .value (.dateRange value) => .ok (.value value)
  | .value _ => .error (.sourceValueKind source)
  | .unknown cause => .ok (.unknown cause)
  | .poison cause => .ok (.poison cause)

/-- Observe one already-read cell at the caller's phase and project it. -/
def observeRange (source : FieldId) (phase : Phase) (cell : CheckedCell) :
    Except DirectDateRangeFault (CellObservation DateRangeCellValue) :=
  projectRange source (observeCell phase cell)

/-- Select one endpoint from an already-observed range. Every endpoint consumer shares this, so a
numeric component read and a verdict-producing comparison cannot disagree about which runtime carrier
is exact; only a malformed checked document reaches the fault. -/
def selectBound (source : FieldId) (bound : DateRangeBound) :
    CellObservation DateRangeCellValue →
    Except DirectDateRangeFault (CellObservation DateValue)
  | .empty => .ok .empty
  | .value (.exact value) => .ok (.value (value.select bound))
  | .value value => .error (.sourceValueProfile source value)
  | .unknown cause => .ok (.unknown cause)
  | .poison cause => .ok (.poison cause)

/-- Read one whole range at the row the environment binds. A declaration crossing no repeatable
level addresses identically at every environment, which is why the root read below can stay a plain
root read rather than routing through this one. -/
def evaluateAt (operation : CheckedDateRangeSource model) (environment : Env)
    (phase : Phase) (input : CheckedDocument model) :
    Except DirectDateRangeFault (CellObservation DateRangeCellValue) := do
  let path ← (environment.pathForScope operation.declaration.repeatableScope)
    |>.mapError .environment
  let cell ← input.read { field := operation.source.id, path }
    |>.mapError .document
  observeRange operation.source.id phase cell

end CheckedDateRangeSource

namespace CheckedDirectDateRange

/-- Read one whole range through the sole immutable checked-document route at the document root. -/
def evaluate (operation : CheckedDirectDateRange model) (phase : Phase)
    (input : CheckedDocument model) :
    Except DirectDateRangeFault (CellObservation DateRangeCellValue) := do
  let cell ← input.read { field := operation.source.id, path := [] }
    |>.mapError .document
  CheckedDateRangeSource.observeRange operation.source.id phase cell

end CheckedDirectDateRange

namespace CheckedDateRangeSourceBound

/-- Read this endpoint's range at the row the environment binds, then select the endpoint. Any
non-exact runtime carrier still fails defensively if a malformed checked document crosses the
static exact-value boundary. -/
def evaluateAt (operation : CheckedDateRangeSourceBound model)
    (environment : Env) (phase : Phase) (input : CheckedDocument model) :
    Except DateRangeBoundFault (CellObservation DateValue) := do
  let observed ←
    operation.toCheckedDateRangeSource.evaluateAt environment phase input
  CheckedDateRangeSource.selectBound operation.source.id operation.bound observed

end CheckedDateRangeSourceBound

namespace CheckedDateRangeBound

/-- The scalar instance: a selection read at the document root. -/
def evaluate (operation : CheckedDateRangeBound model) (phase : Phase)
    (input : CheckedDocument model) :
    Except DateRangeBoundFault (CellObservation DateValue) :=
  operation.toCheckedDateRangeSourceBound.evaluateAt [] phase input

end CheckedDateRangeBound

namespace DateRangeBoundComparisonPosition

/-- Compare one already-projected endpoint against a fixed complete date at its authored side. The
authored side is retained rather than normalized, because the comparison is not symmetric and an
explanation must name the operand the author wrote. -/
def evalAgainstFixed (position : DateRangeBoundComparisonPosition)
    (comparison : TemporalComparisonOp) (expected : FullDate)
    (selected : CellObservation FullDate) : Verdict :=
  match position with
  | .left => comparison.evalObserved selected (.value expected)
  | .right => comparison.evalObserved (.value expected) selected

end DateRangeBoundComparisonPosition

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
  .ok {
    selected
    verdict := operation.position.evalAgainstFixed operation.comparison
      operation.expected projected }

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
