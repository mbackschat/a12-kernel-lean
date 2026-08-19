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

/-- Static refusal while checking the bounded two-direct-field DateRange source. -/
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

/-- One fixed exact DateRange target and exactly two direct nonrepeatable same-group sources sharing its declaration profile. -/
structure CheckedDateRangeFirstFilledDirectComputation (model : FlatModel) where
  private mk ::
  target : CheckedDirectDateRange model
  targetDeclaration : FlatFieldDecl
  shape : CheckedFieldEntityShape model
  first : CheckedDirectDateRange model
  firstDeclaration : FlatFieldDecl
  second : CheckedDirectDateRange model
  secondDeclaration : FlatFieldDecl
  format : DateRangeFormat
  targetGroup : GroupPath
  targetFormat : target.format = .exact format
  firstFormat : first.format = .exact format
  secondFormat : second.format = .exact format
  targetOwnedByGroup : targetDeclaration.groupPath = targetGroup
  firstOwnedByGroup : firstDeclaration.groupPath = targetGroup
  secondOwnedByGroup : secondDeclaration.groupPath = targetGroup
  sourcesExcludeTarget :
    first.source.id ≠ target.source.id ∧ second.source.id ≠ target.source.id

/-- Check the externally measured exact two-direct-field shape through the shared entity-list and direct DateRange owners. -/
def checkDateRangeFirstFilledDirectComputation
    (model : FlatModel) (declaringGroup : GroupPath) (targetField : FieldId)
    (authored : SurfaceFieldEntitySource) :
    Except DateRangeFirstFilledDirectComputationElabError
      (CheckedDateRangeFirstFilledDirectComputation model) := do
  let shape ← elaborateFieldEntityShape model declaringGroup authored
    |>.mapError .sourceShape
  let firstDeclaration ← match shape.first, shape.rest with
    | .field first .stored, [.field _ .stored] => pure first
    | _, _ => throw .unsupportedSourceShape
  let secondDeclaration ← match shape.first, shape.rest with
    | .field _ .stored, [.field second .stored] => pure second
    | _, _ => throw .unsupportedSourceShape
  let targetDeclaration ← model.resolveNonrepeatableDeclarationById targetField
    |>.mapError fun cause => .target (.source cause)
  let target ← elaborateDirectDateRange model targetField |>.mapError .target
  let first ← elaborateDirectDateRange model firstDeclaration.id
    |>.mapError fun cause => .source firstDeclaration.path cause
  let second ← elaborateDirectDateRange model secondDeclaration.id
    |>.mapError fun cause => .source secondDeclaration.path cause
  if hTargetGroup : targetDeclaration.groupPath = declaringGroup then
    if hFirstGroup : firstDeclaration.groupPath = declaringGroup then
      if hSecondGroup : secondDeclaration.groupPath = declaringGroup then
        if hFirstTarget : first.source.id = target.source.id then
          throw (.targetSelfReference firstDeclaration.path)
        else if hSecondTarget : second.source.id = target.source.id then
          throw (.targetSelfReference secondDeclaration.path)
        else
          match hTargetFormat : target.format with
          | .exact targetFormat =>
              match hFirstFormat : first.format with
              | .exact firstFormat =>
                  match hSecondFormat : second.format with
                  | .exact secondFormat =>
                      if hFirstProfile : firstFormat = targetFormat then
                        if hSecondProfile : secondFormat = targetFormat then
                          pure {
                            target
                            targetDeclaration
                            shape
                            first
                            firstDeclaration
                            second
                            secondDeclaration
                            format := targetFormat
                            targetGroup := declaringGroup
                            targetFormat := hTargetFormat
                            firstFormat := by rw [hFirstFormat, hFirstProfile]
                            secondFormat := by rw [hSecondFormat, hSecondProfile]
                            targetOwnedByGroup := hTargetGroup
                            firstOwnedByGroup := hFirstGroup
                            secondOwnedByGroup := hSecondGroup
                            sourcesExcludeTarget := ⟨hFirstTarget, hSecondTarget⟩ }
                        else
                          throw (.varyingProfiles targetDeclaration.path
                            secondDeclaration.path)
                      else
                        throw (.varyingProfiles targetDeclaration.path
                          firstDeclaration.path)
                  | _ =>
                      throw (.unsupportedProfile secondDeclaration.path
                        second.policy.format second.policy.separator)
              | _ =>
                  throw (.unsupportedProfile firstDeclaration.path
                    first.policy.format first.policy.separator)
          | _ =>
              throw (.unsupportedProfile targetDeclaration.path
                target.policy.format target.policy.separator)
      else
        throw (.sourceGroup secondDeclaration.path
          secondDeclaration.groupPath declaringGroup)
    else
      throw (.sourceGroup firstDeclaration.path
        firstDeclaration.groupPath declaringGroup)
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

/-- Scan exactly two direct observations without forcing the second after a terminal first result. -/
def scanTwoDirectDateRangeFirstFilled
    (first : Except ε (CellObservation DateRangeCellValue))
    (second : Unit → Except ε (CellObservation DateRangeCellValue)) :
    Except ε DateRangeFirstFilledResult := do
  let firstObserved ← first
  match DateRangeFirstFilledResult.ofObservation firstObserved with
  | .noValue =>
      DateRangeFirstFilledResult.ofObservation <$> second ()
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

/-- Execute the exact two-field source lazily through the one checked document. A terminal first observation leaves the second field unread. -/
def execute (operation : CheckedDateRangeFirstFilledDirectComputation model)
    (input : CheckedDocument model) :
    Except DateRangeFirstFilledComputationFault DateRangeTargetOutcome := do
  let result ← scanTwoDirectDateRangeFirstFilled
    (operation.first.evaluate .computation input |>.mapError .directSource)
    (fun _ =>
      operation.second.evaluate .computation input |>.mapError .directSource)
  evaluateDateRangeFirstFilledResult (.exact operation.format) result

end CheckedDateRangeFirstFilledDirectComputation

end A12Kernel
