import A12Kernel.Elaboration.DateRangeConstructionComparison
import A12Kernel.Elaboration.DateRangeTargetPresentation
import A12Kernel.Elaboration.TemporalComputationResult

/-! # Checked direct DateRange construction computation -/

namespace A12Kernel

/-- The target presentation certified by a direct construction computation: the target's own
declared input profile, retained rather than re-derived. The former enumeration named only one
spelling per component set and therefore could not represent a `MM` target with the empty
separator or a `dd.MM` target at all, even though both accept a construction of their set. -/
structure DateRangeConstructionTargetFormat where
  input : DateRangeInputFormat
  deriving Repr, DecidableEq

namespace DateRangeConstructionTargetFormat

/-- Recover the checked DateRange declaration profile represented by this construction target. -/
def toInputFormat (format : DateRangeConstructionTargetFormat) :
    DateRangeInputFormat :=
  format.input

/-- Recover the executable target presentation only when the construction and the target expose
the same component set. Lexical spelling does not enter it, so both spellings of each set accept
the construction and the target's own spelling then renders the result. -/
def ofProfiles? (endpoint : DateRangeEndpointFormat)
    (stored : DateRangeInputFormat) :
    Option DateRangeConstructionTargetFormat :=
  if endpoint.matchesStoredInput stored then some { input := stored } else none

/-- Render one resolved range through the checked exact or fragment target presentation. Each constructor is derived from the declaration's exact format/separator pair. -/
def render : DateRangeConstructionTargetFormat → ResolvedDateRange → StoredDateRange
  | format, range => format.toInputFormat.renderResolved range

/-- Consume one typed construction result through its checked target presentation. -/
def evaluateComputationResult (format : DateRangeConstructionTargetFormat) :
    DateRangeComputationResult →
      Except DateRangeTargetEvaluationFault DateRangeTargetOutcome
  | result => format.toInputFormat.evaluateComputationResult result

end DateRangeConstructionTargetFormat

/-- Verify that the model-owned direct DateRange target remains in the computation's declaring group. -/
def FlatModel.ownsDirectDateRangeTarget
    (model : FlatModel) (declaringGroup : GroupPath)
    (target : CheckedDirectDateRange model) : Bool :=
  match model.lookupUniqueId target.source.id with
  | .ok declaration => declaration.groupPath == declaringGroup
  | .error _ => false

/-- Static refusal before one direct DateRange construction can reach its target. -/
inductive DateRangeConstructionComputationElabError where
  | construction (cause : DateRangeConstructionElabError)
  | target (cause : DirectDateRangeElabError)
  | targetGroup (actual expected : GroupPath)
  | endpointFormat (start finish : DateRangeEndpointFormat)
  | incoherentCore
  deriving Repr, DecidableEq

/-- One checked construction and its matching direct nonrepeatable DateRange target. -/
structure CheckedDateRangeConstructionComputation (model : FlatModel) where
  construction : CheckedDateRangeConstruction model
  target : CheckedDirectDateRange model
  declaringGroup : GroupPath
  targetOwnedByGroup : model.ownsDirectDateRangeTarget declaringGroup target = true
  format : DateRangeConstructionTargetFormat
  profileOwned :
    DateRangeConstructionTargetFormat.ofProfiles?
      construction.start.format target.format = some format

/-- Certify one supported construction and matching DateRange target against the same checked model. -/
def elaborateDateRangeConstructionComputation
    (model : FlatModel) (declaringGroup : GroupPath) (targetField : FieldId)
    (start finish : FieldId) :
    Except DateRangeConstructionComputationElabError
      (CheckedDateRangeConstructionComputation model) := do
  let construction ← elaborateDateRangeConstruction model start finish
    |>.mapError .construction
  let targetDeclaration ← model.resolveNonrepeatableDeclarationById targetField
    |>.mapError (fun error => .target (.source error))
  if _hGroup : targetDeclaration.groupPath = declaringGroup then
    let target ← elaborateDirectDateRange model targetField |>.mapError .target
    if hOwned : model.ownsDirectDateRangeTarget declaringGroup target then
      match hFormat : DateRangeConstructionTargetFormat.ofProfiles?
          construction.start.format target.format with
      | some format =>
          pure {
            construction
            target
            declaringGroup
            targetOwnedByGroup := hOwned
            format
            profileOwned := hFormat
          }
      | none =>
          throw (.endpointFormat construction.start.format construction.finish.format)
    else
      throw .incoherentCore
  else
    throw (.targetGroup targetDeclaration.groupPath declaringGroup)

/-- Project one evaluated construction into the shared exact-or-yearless target result while reusing its established formal-before-empty precedence. -/
def DateRangeConstructionObservation.asComputationResult
    (observation : DateRangeConstructionObservation) : DateRangeComputationResult :=
  match observation.comparisonOperand with
  | .notEvaluated => .noValue
  | .unknown cause => .poison cause
  | .value range _ => .value range

inductive DateRangeConstructionComputationFault where
  | construction (cause : DateRangeConstructionFault)
  | target (cause : DateRangeTargetEvaluationFault)
  deriving Repr, DecidableEq

/-- Execute/Analyze/Explain result retaining both endpoint observations beside the typed target outcome. -/
structure DateRangeConstructionComputationResult where
  construction : DateRangeConstructionObservation
  outcome : DateRangeTargetOutcome
  deriving Repr, DecidableEq

namespace CheckedDateRangeConstructionComputation

/-- Read the two checked endpoints once in computation phase, then render their typed range through the checked target policy. -/
def execute (operation : CheckedDateRangeConstructionComputation model)
    (input : CheckedDocument model) :
    Except DateRangeConstructionComputationFault
      DateRangeConstructionComputationResult := do
  let construction ← operation.construction.evaluate .computation input
    |>.mapError .construction
  let outcome ← operation.format.evaluateComputationResult
      construction.asComputationResult
    |>.mapError .target
  pure { construction, outcome }

/-- Execute and classify one rich direct-construction outcome against the same immutable source document. Endpoint observations remain available from `execute`; this result projection reuses the shared DateRange carrier without a second construction representation. -/
def executeResult (operation : CheckedDateRangeConstructionComputation model)
    (input : CheckedDocument model)
    (residualMessages : List ResidualMessage) :
    Except DateRangeConstructionComputationFault
      (DateRangeComputationRunView ResidualMessage) := do
  let result ← operation.execute input
  pure (DateRangeComputationRunView.fromOutcomes input residualMessages
    [(operation.target.source.id, result.outcome)])

end CheckedDateRangeConstructionComputation

end A12Kernel
