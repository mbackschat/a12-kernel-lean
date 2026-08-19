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

/-- Check one of the six admitted matching DateRange declaration profiles without widening operands, nesting, or document architecture. -/
def checkDateRangeFirstFilledComputation
    (model : FlatModel) (declaringGroup : GroupPath) (targetField : FieldId)
    (authored : SurfaceStarFieldPath) :
    Except DateRangeFirstFilledComputationElabError
      (CheckedDateRangeFirstFilledComputation model) := do
  match checkTemporalFirstFilledStarComputation
      model declaringGroup targetField authored .dateRangeIsoSlash with
  | .ok shape => pure (.isoSlash shape)
  | .error (.targetCarrier _) =>
      match checkTemporalFirstFilledStarComputation
          model declaringGroup targetField authored .dateRangeDayMonthYearDash with
      | .ok shape => pure (.dayMonthYearDash shape)
      | .error (.targetCarrier _) =>
          match checkTemporalFirstFilledStarComputation
              model declaringGroup targetField authored .dateRangeYearFragment with
          | .ok shape => pure (.yearFragment shape)
          | .error (.targetCarrier _) =>
              match checkTemporalFirstFilledStarComputation model declaringGroup
                  targetField authored .dateRangeYearMonthFragment with
              | .ok shape => pure (.yearMonthFragment shape)
              | .error (.targetCarrier _) =>
                  match checkTemporalFirstFilledStarComputation model declaringGroup
                      targetField authored .dateRangeMonthFragment with
                  | .ok shape => pure (.monthFragment shape)
                  | .error (.targetCarrier _) =>
                      let shape ← checkTemporalFirstFilledStarComputation
                        model declaringGroup targetField authored
                          .dateRangeMonthDayFragment |>.mapError .shape
                      pure (.monthDayFragment shape)
                  | .error cause => throw (.shape cause)
              | .error cause => throw (.shape cause)
          | .error cause => throw (.shape cause)
      | .error cause => throw (.shape cause)
  | .error cause => throw (.shape cause)

/-- Static refusal while checking the bounded direct-field-list DateRange source. -/
inductive DateRangeFirstFilledDirectComputationElabError where
  | target (cause : DirectDateRangeElabError)
  | source (path : List String) (cause : DirectDateRangeElabError)
  | sourceShape (cause : FieldEntityShapeElabError)
  | unsupportedSourceShape
  | targetGroup (actual expected : GroupPath)
  | sourceGroup (path : List String) (actual expected : GroupPath)
  | unsupportedProfile (path : List String) (format separator : String)
  | varyingProfiles (first second : List String)
  | targetSelfReference (path : List String)
  deriving Repr, DecidableEq

namespace DateRangeFirstFilledDirectComputationElabError

/-- Project the shared entity-list classes, measured exact-profile mismatch, and established target self-reference class. Wider local refusals stay unmapped. -/
def diagnostic? : DateRangeFirstFilledDirectComputationElabError →
    Option KernelStaticDiagnostic
  | .sourceShape cause => cause.diagnostic?
  | .varyingProfiles _ _ => some .varyingTypesNotAllowed
  | .targetSelfReference _ => some .errorReferenceToCalculatedField
  | .target _ | .source _ _ | .unsupportedSourceShape | .targetGroup _ _ |
      .sourceGroup _ _ _ | .unsupportedProfile _ _ _ => none

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

/-- One checked direct source in the target's group and exact declaration profile. -/
structure CheckedDateRangeFirstFilledDirectSource
    (model : FlatModel) (targetField : FieldId) (format : DateRangeFormat)
    (targetGroup : GroupPath) where
  private mk ::
  declaration : FlatFieldDecl
  direct : CheckedDirectDateRange model
  sourceIdentity : direct.source.id = declaration.id
  sourceFormat : direct.format = .exact format
  ownedByGroup : declaration.groupPath = targetGroup
  excludesTarget : direct.source.id ≠ targetField

/-- One fixed exact DateRange target and a finite direct nonrepeatable same-group source list sharing its declaration profile. -/
structure CheckedDateRangeFirstFilledDirectComputation (model : FlatModel) where
  private mk ::
  target : CheckedDirectDateRange model
  targetDeclaration : FlatFieldDecl
  shape : CheckedFieldEntityShape model
  format : DateRangeFormat
  targetGroup : GroupPath
  sources : List (CheckedDateRangeFirstFilledDirectSource model
    target.source.id format targetGroup)
  targetFormat : target.format = .exact format
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
    (format : DateRangeFormat) :
    List (NonselfDateRangeFirstFilledDirectCandidate
      model targetField targetGroup) →
      Except DateRangeFirstFilledDirectComputationElabError
        (List (CheckedDateRangeFirstFilledDirectSource
          model targetField format targetGroup))
  | [] => pure []
  | candidate :: remaining => do
      let grouped := candidate.candidate
      let source := grouped.candidate
      match hFormat : source.direct.format with
      | .exact sourceFormat =>
          if hMatches : sourceFormat = format then
            pure ({
              declaration := source.declaration
              direct := source.direct
              sourceIdentity := source.sourceIdentity
              sourceFormat := by rw [hFormat, hMatches]
              ownedByGroup := grouped.ownedByGroup
              excludesTarget := candidate.excludesTarget
            } :: (← certifyDirectSourceProfiles targetPath format remaining))
          else
            throw (.varyingProfiles targetPath source.declaration.path)
      | _ =>
          throw (.unsupportedProfile source.declaration.path
            source.direct.policy.format source.direct.policy.separator)

/-- Check a finite exact direct-field list through the shared entity-list and direct DateRange owners. External authorability is calibrated at lengths two and three. -/
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
    match hTargetFormat : target.format with
    | .exact targetFormat =>
        let sources ← certifyDirectSourceProfiles
          targetDeclaration.path targetFormat nonself
        pure {
          target
          targetDeclaration
          shape
          format := targetFormat
          targetGroup := declaringGroup
          sources
          targetFormat := hTargetFormat
          targetOwnedByGroup := hTargetGroup }
    | _ =>
        throw (.unsupportedProfile targetDeclaration.path
          target.policy.format target.policy.separator)
  else
    throw (.targetGroup targetDeclaration.groupPath declaringGroup)

/-- Root result retaining exact or yearless DateRange cell identity until the checked target policy consumes it. -/
inductive DateRangeFirstFilledResult where
  | noValue
  | value (range : DateRangeCellValue)
  | poison (cause : FormalCause)
  deriving Repr, DecidableEq

namespace DateRangeFirstFilledResult

/-- Preserve one phase-projected DateRange observation in the common first-filled result domain. -/
def ofObservation : CellObservation DateRangeCellValue → DateRangeFirstFilledResult
  | .empty => .noValue
  | .value range => .value range
  | .unknown cause | .poison cause => .poison cause

end DateRangeFirstFilledResult

/-- Scan a finite direct list without forcing any suffix after a terminal value or formal cause. -/
def scanDirectDateRangeFirstFilled :
    List (Unit → Except ε (CellObservation DateRangeCellValue)) →
      Except ε DateRangeFirstFilledResult
  | [] => pure .noValue
  | observe :: remaining => do
      let observed ← observe ()
      match DateRangeFirstFilledResult.ofObservation observed with
      | .noValue => scanDirectDateRangeFirstFilled remaining
      | result => pure result

/-- Project one checked DateRange cell into the typed root result consumed by the target policy. Source stored text is not selected. -/
def dateRangeFirstFilledCellAt
    (addressed : CheckedAddressedCell) : DateRangeFirstFilledResult :=
  match observeCell .computation addressed.cell with
  | .value (.dateRange range) => .value range
  | .value _ => .poison .malformed
  | .empty => .noValue
  | .unknown cause | .poison cause => .poison cause

/-- Select the first present DateRange or reached formal cause; exhaustion keeps the no-value identity. -/
def evalDateRangeFirstFilledCells :
    List CheckedAddressedCell → DateRangeFirstFilledResult
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

/-- Consume a selected exact or yearless cell through its matching checked declaration profile. -/
private def evaluateDateRangeFirstFilledResult (format : DateRangeInputFormat) :
    DateRangeFirstFilledResult →
      Except DateRangeFirstFilledComputationFault DateRangeTargetOutcome
  | .noValue => .ok .noValue
  | .poison cause => .ok (.poison cause)
  | .value (.exact range) =>
      format.evaluateExactValue range |>.mapError fun
        | .unresolvedEndpoint value => .unresolvedEndpoint value
  | .value (.yearlessMonth start finish) =>
      match format with
      | .yearlessMonth => .ok (.accepted
          (DateRangeInputFormat.renderYearlessMonth start finish))
      | _ => .ok (.poison .malformed)
  | .value (.yearlessMonthDay start finish) =>
      match format with
      | .yearlessMonthDay => .ok (.accepted
          (DateRangeInputFormat.renderYearlessMonthDay start finish))
      | _ => .ok (.poison .malformed)

namespace CheckedDateRangeFirstFilledComputation

/-- Execute one checked carrier through the single document and render its exact or yearless cell through the retained target policy. -/
private def executeWith
    (shape : CheckedTemporalFirstFilledStarComputation model carrier)
    (format : DateRangeInputFormat)
    (input : CheckedDocument model) :
    Except DateRangeFirstFilledComputationFault DateRangeTargetOutcome := do
  let resolved ← shape.source.resolveCheckedField input []
    |>.mapError .source
  evaluateDateRangeFirstFilledResult format
    (evalDateRangeFirstFilledCells resolved.cells)

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

end CheckedDateRangeFirstFilledComputation

namespace CheckedDateRangeFirstFilledDirectComputation

/-- Execute the finite exact direct source list lazily through the one checked document. A terminal observation leaves every suffix field unread. -/
def execute (operation : CheckedDateRangeFirstFilledDirectComputation model)
    (input : CheckedDocument model) :
    Except DateRangeFirstFilledComputationFault DateRangeTargetOutcome := do
  let result ← scanDirectDateRangeFirstFilled
    (operation.sources.map fun source _ =>
      source.direct.evaluate .computation input |>.mapError .directSource)
  evaluateDateRangeFirstFilledResult (.exact operation.format) result

end CheckedDateRangeFirstFilledDirectComputation

end A12Kernel
