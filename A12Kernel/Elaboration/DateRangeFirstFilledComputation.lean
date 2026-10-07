import A12Kernel.Elaboration.TemporalFirstFilledShape
import A12Kernel.Elaboration.DateRangeTargetPresentation
import A12Kernel.Elaboration.DateRangeBound
import A12Kernel.Elaboration.FieldEntityList
import A12Kernel.Elaboration.TemporalErroredComputationApplication
import A12Kernel.Elaboration.ComputationFormalInput
import A12Kernel.Semantics.TemporalTarget

/-! # Bounded DateRange `FirstFilledValue` computations

Starred and selected entity-list sources use the shared temporal site at fixed or repeatable targets. A direct list
of plain fields at a fixed target is its own carrier, which owns the list's measured profile classes.
-/

namespace A12Kernel

inductive DateRangeFirstFilledComputationElabError where
  | shape (cause : TemporalFirstFilledSiteElabError)
  | targetNotDateRange (path : List String)
  deriving Repr, DecidableEq

/-- The input format a DateRange carrier names; a scalar temporal carrier names none. -/
def TemporalFirstFilledStarCarrier.dateRangeFormat? :
    TemporalFirstFilledStarCarrier → Option DateRangeInputFormat
  | .dateRangeIsoSlash => some (.exact .isoSlash)
  | .dateRangeDayMonthYearDash => some (.exact .dayMonthYearDash)
  | .dateRangeYearFragment => some .yearFragment
  | .dateRangeYearMonthFragment => some .yearMonthFragment
  | .dateRangeMonthFragment => some .yearlessMonth
  | .dateRangeMonthDayFragment => some .yearlessMonthDay
  | .dateRangeMonthConcatenated => some .yearlessMonthConcatenated
  | .dateRangeDayMonthDotted => some .yearlessDayMonthDotted
  | _ => none

/-- One DateRange target, fixed or repeatable, and one starred source whose declared profile exposes
the target's component set; the target's own format renders the selected range. -/
structure CheckedDateRangeFirstFilledComputation (model : FlatModel) where
  private mk ::
  shape : CheckedTemporalFirstFilledSite model
  format : DateRangeInputFormat
  formatOwned : shape.carrier.dateRangeFormat? = some format

/-- Check a star or selected entity-list DateRange source through the shared placed carrier. -/
def checkDateRangeFirstFilledSourceComputation
    (model : FlatModel) (declaringGroup : GroupPath) (targetField : FieldId)
    (authored : SurfaceFirstFilledSource) :
    Except DateRangeFirstFilledComputationElabError
      (CheckedDateRangeFirstFilledComputation model) := do
  let shape ← (checkTemporalFirstFilledSite model declaringGroup targetField authored).mapError
    .shape
  match formatOwned : shape.carrier.dateRangeFormat? with
  | some format => pure { shape, format, formatOwned }
  | none => throw (.targetNotDateRange shape.site.target.path)

/-- Preserve the direct-star entry point used by existing callers. -/
def checkDateRangeFirstFilledComputation
    (model : FlatModel) (declaringGroup : GroupPath) (targetField : FieldId)
    (authored : SurfaceStarFieldPath) :=
  checkDateRangeFirstFilledSourceComputation model declaringGroup targetField (.star authored)

/-- Static refusal while checking the bounded direct-field-list DateRange source. -/
inductive DateRangeFirstFilledDirectComputationElabError where
  | target (cause : DirectDateRangeElabError)
  | source (path : List String) (cause : DirectDateRangeElabError)
  | sourceShape (cause : FieldEntityShapeElabError)
  | unsupportedSourceShape
  | varyingProfiles (first second : List String)
  | targetProfileNotComparable (target : List String)
      (source : DateRangeInputFormat)
  | targetSelfReference (path : List String)
  deriving Repr, DecidableEq

namespace DateRangeFirstFilledDirectComputationElabError

/-- Project the shared entity-list classes, measured profile mismatch, and established target
self-reference class.

The three unmapped arms are named rather than wildcarded and are not one kind of thing. `target` is
resolution routing and claims nothing by construction. `source` and `unsupportedSourceShape` are
this carrier's own representation limits — a source shape it declines to certify — so the Kernel's
treatment of them is unmeasured rather than absent, and each is a measurement target the moment a
consumer needs the class. -/
def diagnostic? : DateRangeFirstFilledDirectComputationElabError →
    Option KernelStaticDiagnostic
  | .sourceShape cause => cause.diagnostic?
  | .varyingProfiles _ _ => some .varyingTypesNotAllowed
  | .targetProfileNotComparable _ _ => some .invalidCompareToDateRange
  | .targetSelfReference _ => some .errorReferenceToCalculatedField
  | .target _ | .source _ _ | .unsupportedSourceShape => none

end DateRangeFirstFilledDirectComputationElabError

private structure DateRangeFirstFilledDirectCandidate (model : FlatModel) where
  declaration : FlatFieldDecl
  direct : CheckedDirectDateRange model
  sourceIdentity : direct.source.id = declaration.id

private structure NonselfDateRangeFirstFilledDirectCandidate
    (model : FlatModel) (targetField : FieldId) where
  candidate : DateRangeFirstFilledDirectCandidate model
  excludesTarget : candidate.direct.source.id ≠ targetField

/-- One checked direct source sharing the list's one declared profile. Every source must expose the identical declared format; the shared format only has to expose the *target's* component set, so a lexical cross between the list and its target is admitted while a cross inside the list is not.

A source carries **no placement requirement**: it need not lie in the declaring group, and two sources of one list need not share a group. Nothing in a direct nonrepeatable list iterates, so the Kernel's containment gate cannot fire on either side ([checkpoint](../../docs/SOURCES.md#src-date-range-direct-list-cross-group-sources)). -/
structure CheckedDateRangeFirstFilledDirectSource
    (model : FlatModel) (targetField : FieldId) (format : DateRangeInputFormat)
    where
  private mk ::
  declaration : FlatFieldDecl
  direct : CheckedDirectDateRange model
  sourceIdentity : direct.source.id = declaration.id
  sourceFormat : direct.format = format
  excludesTarget : direct.source.id ≠ targetField

/-- One fixed DateRange target and a finite direct nonrepeatable same-group source list sharing its declaration profile. -/
structure CheckedDateRangeFirstFilledDirectComputation (model : FlatModel) where
  private mk ::
  target : CheckedDirectDateRange model
  targetDeclaration : FlatFieldDecl
  shape : CheckedFieldEntityShape model
  format : DateRangeInputFormat
  /-- The group the computation is declared in, which the target need not lie in or below. -/
  declaringGroup : GroupPath
  /-- That group is representable. Every operand kind's resolution guards it, so the certificate
      carries the fact rather than leaving a consumer to re-test a path this shape already walked. -/
  declaringGroupValid : GroupPath.isValid declaringGroup = true
  sources : List (CheckedDateRangeFirstFilledDirectSource model
    target.source.id format)
  targetComparable : target.format.components = format.components

private def directStoredDeclarations (model : FlatModel) :
    List (ResolvedFieldEntityOperand model) →
      Except DateRangeFirstFilledDirectComputationElabError
        (List FlatFieldDecl)
  | [] => pure []
  | .field declaration .stored :: remaining => do
      pure (declaration :: (← directStoredDeclarations model remaining))
  | _ :: _ => throw .unsupportedSourceShape

private def elaborateDirectCandidates (model : FlatModel) :
    List FlatFieldDecl →
      Except DateRangeFirstFilledDirectComputationElabError
        (List (DateRangeFirstFilledDirectCandidate model))
  | [] => pure []
  | declaration :: remaining => do
      let direct ← elaborateDirectDateRange model declaration.id
        |>.mapError fun cause => .source declaration.path cause
      if hIdentity : direct.source.id = declaration.id then
        pure ({ declaration, direct, sourceIdentity := hIdentity } ::
          (← elaborateDirectCandidates model remaining))
      else
        throw (.source declaration.path .incoherentCore)

private def certifyDirectSourcesExcludeTarget (targetField : FieldId) :
    List (DateRangeFirstFilledDirectCandidate model) →
      Except DateRangeFirstFilledDirectComputationElabError
        (List (NonselfDateRangeFirstFilledDirectCandidate model targetField))
  | [] => pure []
  | candidate :: remaining => do
      if hExcludes : candidate.direct.source.id = targetField then
        throw (.targetSelfReference candidate.declaration.path)
      else
        pure ({ candidate, excludesTarget := hExcludes } ::
          (← certifyDirectSourcesExcludeTarget targetField remaining))

private def certifyDirectSourceProfiles (targetPath : List String)
    (format : DateRangeInputFormat) :
    List (NonselfDateRangeFirstFilledDirectCandidate model targetField) →
      Except DateRangeFirstFilledDirectComputationElabError
        (List (CheckedDateRangeFirstFilledDirectSource
          model targetField format))
  | [] => pure []
  | candidate :: remaining => do
      let source := candidate.candidate
      if hMatches : source.direct.format = format then
        pure ({
          declaration := source.declaration
          direct := source.direct
          sourceIdentity := source.sourceIdentity
          sourceFormat := hMatches
          excludesTarget := candidate.excludesTarget
        } :: (← certifyDirectSourceProfiles targetPath format remaining))
      else
        throw (.varyingProfiles targetPath source.declaration.path)

/-- Check a finite direct-field list through the shared entity-list and direct DateRange owners. External authorability is calibrated at lengths two and three. -/
def checkDateRangeFirstFilledDirectComputation
    (model : FlatModel) (declaringGroup : GroupPath) (targetField : FieldId)
    (authored : SurfaceFieldEntitySource) :
    Except DateRangeFirstFilledDirectComputationElabError
      (CheckedDateRangeFirstFilledDirectComputation model) :=
  -- Matched rather than bound, so the shape's own group guard is available as the certificate's
  -- validity field instead of being re-tested on a path this resolution already walked.
  -- The target's group places a refusal, as on every measured computation carrier
  -- ([checkpoint](../../docs/sources/group-list-and-capacity-probes.md#src-walk-batch-reading-scope)).
  -- The target resolves after the shape, so an unresolvable one leaves the declaring group to
  -- place it until its own gate refuses.
  let targetGroup := ((model.lookupUniqueId targetField).toOption.map (·.groupPath)).getD declaringGroup
  match hShape : elaborateFieldEntityShape model declaringGroup authored
      (writtenGroup := targetGroup) with
  | .error error => .error (.sourceShape error)
  | .ok shape => do
  let sourceDeclarations ← directStoredDeclarations model shape.operands
  let targetDeclaration ← model.resolveNonrepeatableDeclarationById targetField
    |>.mapError fun cause => .target (.source cause)
  let target ← elaborateDirectDateRange model targetField |>.mapError .target
  let candidates ← elaborateDirectCandidates model sourceDeclarations
  -- No placement test on either side. The list is a direct read of nonrepeatable fields, so
  -- nothing iterates and the Kernel's containment gate cannot fire: the target may sit in an
  -- unrelated group, and so may each source, including in two different groups from each other.
  let nonself ← certifyDirectSourcesExcludeTarget target.source.id candidates
  -- The list's own profile leads: every source must repeat the first one's exact declared
  -- format, and only that shared format is then compared with the target. An empty list has
  -- no profile of its own, so the target's stands in and the comparison is trivial.
  let sharedFormat := match nonself with
    | [] => target.format
    | candidate :: _ => candidate.candidate.direct.format
  let sources ← certifyDirectSourceProfiles
    targetDeclaration.path sharedFormat nonself
  if hComparable : target.format.components = sharedFormat.components then
    pure {
      target
      targetDeclaration
      shape
      format := sharedFormat
      declaringGroup
      declaringGroupValid := elaborateFieldEntityShape_declaringGroupValid hShape
      sources
      targetComparable := hComparable }
  else
    throw (.targetProfileNotComparable targetDeclaration.path sharedFormat)

/-- Preserve one phase-projected DateRange observation in the common first-filled result domain. -/
private def dateRangeFirstFilledResultOfObservation :
    CellObservation DateRangeCellValue → DateRangeComputationResult
  | .empty => .noValue
  | .value range => .value range
  | .unknown cause | .poison cause => .poison cause

/-- Scan a finite direct list without forcing any suffix after a terminal value or formal cause. -/
def scanDirectDateRangeFirstFilled :
    List (Unit → Except ε (CellObservation DateRangeCellValue)) →
      Except ε DateRangeComputationResult
  | [] => pure .noValue
  | observe :: remaining => do
      let observed ← observe ()
      match dateRangeFirstFilledResultOfObservation observed with
      | .noValue => scanDirectDateRangeFirstFilled remaining
      | result => pure result

/-- Project one checked DateRange cell into the typed root result consumed by the target policy. Source stored text is not selected. -/
def dateRangeFirstFilledCellAt
    (addressed : CheckedAddressedCell) : DateRangeComputationResult :=
  match observeCell .computation addressed.cell with
  | .value (.dateRange range) => .value range
  | .value _ => .poison .malformed
  | .empty => .noValue
  | .unknown cause | .poison cause => .poison cause

/-- Select the first present DateRange or reached formal cause; exhaustion keeps the no-value identity. -/
def evalDateRangeFirstFilledCells :
    List CheckedAddressedCell → DateRangeComputationResult
  | [] => .noValue
  | addressed :: remaining =>
      match dateRangeFirstFilledCellAt addressed with
      | .noValue => evalDateRangeFirstFilledCells remaining
      | result => result

inductive DateRangeFirstFilledComputationFault where
  | site (cause : FirstFilledSiteFault)
  | directSource (cause : DirectDateRangeFault)
  | unresolvedEndpoint (range : DateRangeValue)
  deriving Repr, DecidableEq

/-- One instance's DateRange selection retained under its exact target address. -/
structure DateRangeFirstFilledComputationOutcome where
  targetField : CellAddr
  outcome : DateRangeTargetOutcome
  deriving Repr, DecidableEq

/-- One checked starred DateRange result backed by the common DateRange channels over exact cell
addresses. -/
structure DateRangeFirstFilledComputationRunView (model : FlatModel) (ResidualMessage : Type) where
  private mk ::
  operation : CheckedDateRangeFirstFilledComputation model
  dateRange : DateRangeComputationRunView ResidualMessage CellAddr

namespace CheckedDateRangeFirstFilledComputation

def targetField (operation : CheckedDateRangeFirstFilledComputation model) : FieldId :=
  operation.shape.site.targetField

def target (operation : CheckedDateRangeFirstFilledComputation model) : FlatFieldDecl :=
  operation.shape.site.target

def referencesField (operation : CheckedDateRangeFirstFilledComputation model) : FieldId → Bool :=
  operation.shape.site.referencesField

theorem excludesTarget (operation : CheckedDateRangeFirstFilledComputation model) :
    operation.referencesField operation.targetField = false :=
  operation.shape.excludesTarget

/-- Scan the source at one target instance's environment, then render the selected exact or
yearless cell through the target's format. -/
def evaluateAt (operation : CheckedDateRangeFirstFilledComputation model)
    (input : CheckedDocument model) (read : CellAddr → Except CheckedDocumentError CheckedCell)
    (target : CellAddr) (environment : Env) (world : Option World := none) :
    Except DateRangeFirstFilledComputationFault DateRangeFirstFilledComputationOutcome := do
  let resolved ← (operation.shape.site.source.resolveAt input read environment world).mapError
    (.site ∘ .source)
  let outcome ← (operation.format.evaluateComputationResult
      (evaluateFirstFilledSource resolved .poison (fun resolved => evalDateRangeFirstFilledCells resolved.cells))).mapError fun
    | .unresolvedEndpoint value => .unresolvedEndpoint value
  pure { targetField := target, outcome }

/-- Run at the fixed target's single instance, or at every instantiated row of a repeatable target's
scope with a clear at each over-limit row. -/
def executeWithRead (operation : CheckedDateRangeFirstFilledComputation model)
    (input : CheckedDocument model) (read : CellAddr → Except CheckedDocumentError CheckedCell)
    (world : Option World := none) :
    Except DateRangeFirstFilledComputationFault (List DateRangeFirstFilledComputationOutcome) :=
  operation.shape.site.instances input (.site ∘ .targetRows) (.site ∘ .targetEnvironment)
    (fun target _ => pure { targetField := target, outcome := .noValue })
    (operation.evaluateAt (world := world) input read)

def execute (operation : CheckedDateRangeFirstFilledComputation model)
    (input : CheckedDocument model) (world : Option World := none) :
    Except DateRangeFirstFilledComputationFault (List DateRangeFirstFilledComputationOutcome) :=
  operation.executeWithRead input input.read world

/-- Classify caller-view outcomes against immutable source target state through the shared DateRange
result owner. -/
def executeResultWithRead (operation : CheckedDateRangeFirstFilledComputation model)
    (input : CheckedDocument model) (read : CellAddr → Except CheckedDocumentError CheckedCell)
    (residualMessages : List ResidualMessage) (world : Option World := none) :
    Except DateRangeFirstFilledComputationFault
      (DateRangeFirstFilledComputationRunView model ResidualMessage) := do
  let outcomes ← operation.executeWithRead input read world
  pure { operation
         dateRange := DateRangeComputationRunView.fromOutcomesAt input.sourceDateRangeTargetStateAt
           residualMessages (outcomes.map fun entry => (entry.targetField, entry.outcome)) }

def executeResult (operation : CheckedDateRangeFirstFilledComputation model)
    (input : CheckedDocument model) (residualMessages : List ResidualMessage) (world : Option World := none) :
    Except DateRangeFirstFilledComputationFault
      (DateRangeFirstFilledComputationRunView model ResidualMessage) :=
  operation.executeResultWithRead input input.read residualMessages world

end CheckedDateRangeFirstFilledComputation

namespace DateRangeFirstFilledComputationRunView

/-- Apply retained source-relative actions to exact DateRange cell-state projections from a separate
checked document of the same model. -/
def applyToChecked (view : DateRangeFirstFilledComputationRunView model ResidualMessage)
    (destination : CheckedDocument model) :
    Except (DateRangeComputationRunView.DateRangeComputationRunApplicationError CellAddr)
      (DateRangeComputationDestination CellAddr) :=
  view.dateRange.applyTo destination.sourceDateRangeTargetStateAt

end DateRangeFirstFilledComputationRunView

/-- Failure while composing selected formal-input preparation with starred DateRange
`FirstFilledValue`. -/
abbrev DateRangeFirstFilledCheckedResultFault := ComputationFormalInputRunFault DateRangeFirstFilledComputationFault

namespace CheckedDateRangeFirstFilledComputation

/-- Bind every source declaration and the computed target to the shared eager inventory. -/
def formalInputPlan (operation : CheckedDateRangeFirstFilledComputation model) :
    Except ComputationFormalInputPlanError (CheckedComputationFormalInputPlan model) :=
  operation.shape.site.formalInputPlan

/-- Prepare the selected sources once, retain every eager finding, and run lazily through the
prepared read. -/
def executeResultWithFormalInputs (operation : CheckedDateRangeFirstFilledComputation model)
    (input : CheckedDocument model) (world : Option World := none) :
    Except DateRangeFirstFilledCheckedResultFault
      (DateRangeFirstFilledComputationRunView model ComputationFormalInputFinding) :=
  runWithFormalInputs operation.formalInputPlan input (operation.executeResultWithRead (world := world) input)

end CheckedDateRangeFirstFilledComputation

namespace CheckedDateRangeFirstFilledDirectComputation

/-- Execute the finite direct source list lazily through the one checked document. A terminal observation leaves every suffix field unread. -/
def execute (operation : CheckedDateRangeFirstFilledDirectComputation model)
    (input : CheckedDocument model) :
    Except DateRangeFirstFilledComputationFault DateRangeTargetOutcome := do
  let result ← scanDirectDateRangeFirstFilled
    (operation.sources.map fun source _ =>
      source.direct.evaluate .computation input |>.mapError .directSource)
  -- The target's own declared spelling renders the selected value, which is what makes an
  -- admitted lexical cross observable: the source profile decides nothing about the output.
  operation.target.format.evaluateComputationResult result |>.mapError fun
    | .unresolvedEndpoint value => .unresolvedEndpoint value

/-- Execute and classify the one checked direct-list outcome against the same immutable source document. Residual messages remain already-classified opaque input. -/
def executeResult
    (operation : CheckedDateRangeFirstFilledDirectComputation model)
    (input : CheckedDocument model)
    (residualMessages : List ResidualMessage) :
    Except DateRangeFirstFilledComputationFault
      (DateRangeComputationRunView ResidualMessage) := do
  let outcome ← operation.execute input
  pure (DateRangeComputationRunView.fromOutcomes input residualMessages
    [(operation.target.source.id, outcome)])

end CheckedDateRangeFirstFilledDirectComputation

end A12Kernel
