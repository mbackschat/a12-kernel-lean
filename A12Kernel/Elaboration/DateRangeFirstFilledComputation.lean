import A12Kernel.Elaboration.TemporalFirstFilledStarComputation
import A12Kernel.Elaboration.DateRangeTargetPresentation
import A12Kernel.Elaboration.DateRangeBound
import A12Kernel.Elaboration.FieldEntityList
import A12Kernel.Elaboration.TemporalErroredComputationApplication
import A12Kernel.Semantics.TemporalTarget

/-! # Bounded DateRange `FirstFilledValue` computations -/

namespace A12Kernel

inductive DateRangeFirstFilledComputationElabError where
  | shape (cause : TemporalFirstFilledStarComputationElabError)
  deriving Repr, DecidableEq

/-- One fixed DateRange target and one direct single-level starred source sharing one admitted declaration profile. -/
inductive CheckedDateRangeFirstFilledComputation (model : FlatModel) where
  | isoSlash
      (shape : CheckedTemporalFirstFilledStarComputation model .dateRangeIsoSlash)
  | dayMonthYearDash
      (shape : CheckedTemporalFirstFilledStarComputation model .dateRangeDayMonthYearDash)
  | yearFragment
      (shape : CheckedTemporalFirstFilledStarComputation model .dateRangeYearFragment)
  | yearMonthFragment
      (shape : CheckedTemporalFirstFilledStarComputation model .dateRangeYearMonthFragment)
  | monthFragment
      (shape : CheckedTemporalFirstFilledStarComputation model .dateRangeMonthFragment)
  | monthDayFragment
      (shape : CheckedTemporalFirstFilledStarComputation model .dateRangeMonthDayFragment)
  | monthConcatenated
      (shape :
        CheckedTemporalFirstFilledStarComputation model .dateRangeMonthConcatenated)
  | dayMonthDotted
      (shape :
        CheckedTemporalFirstFilledStarComputation model .dateRangeDayMonthDotted)

/-- Offer one admitted declaration profile for the authored target. A target-carrier mismatch means "not this profile", so the caller may offer the next one; every other refusal is reached before the carrier comparison and is therefore shared by all profiles. -/
private def offerDateRangeFirstFilledCarrier (model : FlatModel)
    (declaringGroup : GroupPath) (targetField : FieldId)
    (authored : SurfaceStarFieldPath)
    (carrier : TemporalFirstFilledStarCarrier)
    (wrap : CheckedTemporalFirstFilledStarComputation model carrier →
      CheckedDateRangeFirstFilledComputation model) :
    Except TemporalFirstFilledStarComputationElabError
      (Option (CheckedDateRangeFirstFilledComputation model)) :=
  match checkTemporalFirstFilledStarComputation model declaringGroup targetField
      authored carrier with
  | .ok shape => pure (some (wrap shape))
  | .error (.targetCarrier _) => pure none
  | .error cause => throw cause

/-- Take the first offered profile that owns the target, preserving authored offer order. -/
private def firstOfferedDateRangeFirstFilled {model : FlatModel} :
    List (Unit → Except TemporalFirstFilledStarComputationElabError
      (Option (CheckedDateRangeFirstFilledComputation model))) →
    Except TemporalFirstFilledStarComputationElabError
      (Option (CheckedDateRangeFirstFilledComputation model))
  | [] => pure none
  | offer :: rest => do
      match ← offer () with
      | some checked => pure (some checked)
      | none => firstOfferedDateRangeFirstFilled rest

/-- Check one of the admitted matching DateRange declaration profiles without widening operands, nesting, or document architecture. -/
def checkDateRangeFirstFilledComputation
    (model : FlatModel) (declaringGroup : GroupPath) (targetField : FieldId)
    (authored : SurfaceStarFieldPath) :
    Except DateRangeFirstFilledComputationElabError
      (CheckedDateRangeFirstFilledComputation model) := do
  let offer := offerDateRangeFirstFilledCarrier model declaringGroup targetField authored
  let offered ← firstOfferedDateRangeFirstFilled [
      fun _ => offer .dateRangeIsoSlash .isoSlash,
      fun _ => offer .dateRangeDayMonthYearDash .dayMonthYearDash,
      fun _ => offer .dateRangeYearFragment .yearFragment,
      fun _ => offer .dateRangeYearMonthFragment .yearMonthFragment,
      fun _ => offer .dateRangeMonthFragment .monthFragment,
      fun _ => offer .dateRangeMonthDayFragment .monthDayFragment,
      fun _ => offer .dateRangeMonthConcatenated .monthConcatenated,
      fun _ => offer .dateRangeDayMonthDotted .dayMonthDotted
    ] |>.mapError .shape
  match offered with
  | some checked => pure checked
  | none =>
      -- Every profile reached the carrier comparison, so the target resolves here; the
      -- repeated lookup only names the target that owns no admitted profile.
      let target ← model.lookupUniqueId targetField
        |>.mapError fun cause => .shape (.target cause)
      throw (.shape (.targetCarrier target.path))

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

/-- Project the shared entity-list classes, measured profile mismatch, and established target self-reference class. Wider local refusals stay unmapped. -/
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
      (CheckedDateRangeFirstFilledDirectComputation model) := do
  let shape ← elaborateFieldEntityShape model declaringGroup authored
    |>.mapError .sourceShape
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
  | source (cause : CheckedStarDocumentError)
  | directSource (cause : DirectDateRangeFault)
  | unresolvedEndpoint (range : DateRangeValue)
  deriving Repr, DecidableEq

namespace CheckedDateRangeFirstFilledComputation

/-- Recover the exact fixed target certificate from every admitted direct-star carrier. -/
def targetDeclaration :
    CheckedDateRangeFirstFilledComputation model → FlatFieldDecl
  | .isoSlash shape => shape.target
  | .dayMonthYearDash shape => shape.target
  | .yearFragment shape => shape.target
  | .yearMonthFragment shape => shape.target
  | .monthFragment shape => shape.target
  | .monthDayFragment shape => shape.target
  | .monthConcatenated shape => shape.target
  | .dayMonthDotted shape => shape.target

/-- Execute one checked carrier through the single document and render its exact or yearless cell through the retained target policy. -/
private def executeWith
    (shape : CheckedTemporalFirstFilledStarComputation model carrier)
    (format : DateRangeInputFormat)
    (input : CheckedDocument model) :
    Except DateRangeFirstFilledComputationFault DateRangeTargetOutcome := do
  let resolved ← shape.source.resolveCheckedField input []
    |>.mapError .source
  format.evaluateComputationResult
      (evalDateRangeFirstFilledCells resolved.cells)
    |>.mapError fun
      | .unresolvedEndpoint value => .unresolvedEndpoint value

/-- Execute through the single checked document and the target policy retained during assembly. -/
def execute (operation : CheckedDateRangeFirstFilledComputation model)
    (input : CheckedDocument model) :
    Except DateRangeFirstFilledComputationFault DateRangeTargetOutcome :=
  match operation with
  | .isoSlash shape => executeWith shape (.exact .isoSlash) input
  | .dayMonthYearDash shape => executeWith shape (.exact .dayMonthYearDash) input
  | .yearFragment shape => executeWith shape .yearFragment input
  | .yearMonthFragment shape => executeWith shape .yearMonthFragment input
  | .monthFragment shape => executeWith shape .yearlessMonth input
  | .monthDayFragment shape => executeWith shape .yearlessMonthDay input
  | .monthConcatenated shape =>
      executeWith shape .yearlessMonthConcatenated input
  | .dayMonthDotted shape => executeWith shape .yearlessDayMonthDotted input

/-- Execute and classify the one checked direct-star outcome against the same immutable source document. Residual messages remain already-classified opaque input. -/
def executeResult (operation : CheckedDateRangeFirstFilledComputation model)
    (input : CheckedDocument model)
    (residualMessages : List ResidualMessage) :
    Except DateRangeFirstFilledComputationFault
      (DateRangeComputationRunView ResidualMessage) := do
  let outcome ← operation.execute input
  pure (DateRangeComputationRunView.fromOutcomes input residualMessages
    [(operation.targetDeclaration.id, outcome)])

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
