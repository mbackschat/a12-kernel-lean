import A12Kernel.Elaboration.TemporalFirstFilledStarComputation
import A12Kernel.Elaboration.DateRangeTargetPresentation
import A12Kernel.Elaboration.DateRangeBound
import A12Kernel.Elaboration.FieldEntityList
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
  | targetGroup (actual expected : GroupPath)
  | sourceGroup (path : List String) (actual expected : GroupPath)
  | varyingProfiles (first second : List String)
  | targetSelfReference (path : List String)
  deriving Repr, DecidableEq

namespace DateRangeFirstFilledDirectComputationElabError

/-- Project the shared entity-list classes, measured profile mismatch, and established target self-reference class. Wider local refusals stay unmapped. -/
def diagnostic? : DateRangeFirstFilledDirectComputationElabError →
    Option KernelStaticDiagnostic
  | .sourceShape cause => cause.diagnostic?
  | .varyingProfiles _ _ => some .varyingTypesNotAllowed
  | .targetSelfReference _ => some .errorReferenceToCalculatedField
  | .target _ | .source _ _ | .unsupportedSourceShape | .targetGroup _ _ |
      .sourceGroup _ _ _ => none

end DateRangeFirstFilledDirectComputationElabError

private structure DateRangeFirstFilledDirectCandidate (model : FlatModel) where
  declaration : FlatFieldDecl
  direct : CheckedDirectDateRange model
  sourceIdentity : direct.source.id = declaration.id

private structure GroupedDateRangeFirstFilledDirectCandidate
    (model : FlatModel) (targetGroup : GroupPath) where
  candidate : DateRangeFirstFilledDirectCandidate model
  ownedByGroup : candidate.declaration.groupPath = targetGroup

private structure NonselfDateRangeFirstFilledDirectCandidate
    (model : FlatModel) (targetField : FieldId) (targetGroup : GroupPath) where
  candidate : GroupedDateRangeFirstFilledDirectCandidate model targetGroup
  excludesTarget : candidate.candidate.direct.source.id ≠ targetField

/-- One checked direct source in the target's group and declaration profile. -/
structure CheckedDateRangeFirstFilledDirectSource
    (model : FlatModel) (targetField : FieldId) (format : DateRangeInputFormat)
    (targetGroup : GroupPath) where
  private mk ::
  declaration : FlatFieldDecl
  direct : CheckedDirectDateRange model
  sourceIdentity : direct.source.id = declaration.id
  sourceFormat : direct.format = format
  ownedByGroup : declaration.groupPath = targetGroup
  excludesTarget : direct.source.id ≠ targetField

/-- One fixed DateRange target and a finite direct nonrepeatable same-group source list sharing its declaration profile. -/
structure CheckedDateRangeFirstFilledDirectComputation (model : FlatModel) where
  private mk ::
  target : CheckedDirectDateRange model
  targetDeclaration : FlatFieldDecl
  shape : CheckedFieldEntityShape model
  format : DateRangeInputFormat
  targetGroup : GroupPath
  sources : List (CheckedDateRangeFirstFilledDirectSource model
    target.source.id format targetGroup)
  targetFormat : target.format = format
  targetOwnedByGroup : targetDeclaration.groupPath = targetGroup

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

private def certifyDirectSourceGroups (targetGroup : GroupPath) :
    List (DateRangeFirstFilledDirectCandidate model) →
      Except DateRangeFirstFilledDirectComputationElabError
        (List (GroupedDateRangeFirstFilledDirectCandidate model targetGroup))
  | [] => pure []
  | candidate :: remaining => do
      if hOwned : candidate.declaration.groupPath = targetGroup then
        pure ({ candidate, ownedByGroup := hOwned } ::
          (← certifyDirectSourceGroups targetGroup remaining))
      else
        throw (.sourceGroup candidate.declaration.path
          candidate.declaration.groupPath targetGroup)

private def certifyDirectSourcesExcludeTarget (targetField : FieldId) :
    List (GroupedDateRangeFirstFilledDirectCandidate model targetGroup) →
      Except DateRangeFirstFilledDirectComputationElabError
        (List (NonselfDateRangeFirstFilledDirectCandidate
          model targetField targetGroup))
  | [] => pure []
  | candidate :: remaining => do
      if hExcludes : candidate.candidate.direct.source.id = targetField then
        throw (.targetSelfReference candidate.candidate.declaration.path)
      else
        pure ({ candidate, excludesTarget := hExcludes } ::
          (← certifyDirectSourcesExcludeTarget targetField remaining))

private def certifyDirectSourceProfiles (targetPath : List String)
    (format : DateRangeInputFormat) :
    List (NonselfDateRangeFirstFilledDirectCandidate
      model targetField targetGroup) →
      Except DateRangeFirstFilledDirectComputationElabError
        (List (CheckedDateRangeFirstFilledDirectSource
          model targetField format targetGroup))
  | [] => pure []
  | candidate :: remaining => do
      let grouped := candidate.candidate
      let source := grouped.candidate
      if hMatches : source.direct.format = format then
        pure ({
          declaration := source.declaration
          direct := source.direct
          sourceIdentity := source.sourceIdentity
          sourceFormat := hMatches
          ownedByGroup := grouped.ownedByGroup
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
  if hTargetGroup : targetDeclaration.groupPath = declaringGroup then
    let grouped ← certifyDirectSourceGroups declaringGroup candidates
    let nonself ← certifyDirectSourcesExcludeTarget target.source.id grouped
    let sources ← certifyDirectSourceProfiles
      targetDeclaration.path target.format nonself
    pure {
      target
      targetDeclaration
      shape
      format := target.format
      targetGroup := declaringGroup
      sources
      targetFormat := rfl
      targetOwnedByGroup := hTargetGroup }
  else
    throw (.targetGroup targetDeclaration.groupPath declaringGroup)

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

end CheckedDateRangeFirstFilledComputation

namespace CheckedDateRangeFirstFilledDirectComputation

/-- Execute the finite direct source list lazily through the one checked document. A terminal observation leaves every suffix field unread. -/
def execute (operation : CheckedDateRangeFirstFilledDirectComputation model)
    (input : CheckedDocument model) :
    Except DateRangeFirstFilledComputationFault DateRangeTargetOutcome := do
  let result ← scanDirectDateRangeFirstFilled
    (operation.sources.map fun source _ =>
      source.direct.evaluate .computation input |>.mapError .directSource)
  operation.format.evaluateComputationResult result |>.mapError fun
    | .unresolvedEndpoint value => .unresolvedEndpoint value

end CheckedDateRangeFirstFilledDirectComputation

end A12Kernel
