import A12Kernel.Elaboration.AddressedRepeatableTarget
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

/-- Static refusal before one direct DateRange construction can reach its target. -/
inductive DateRangeConstructionComputationElabError where
  | construction (cause : DateRangeConstructionElabError)
  | target (cause : DirectDateRangeElabError)
  | endpointFormat (start finish : DateRangeEndpointFormat)
  | incoherentCore
  deriving Repr, DecidableEq

/-- One checked construction and its matching direct nonrepeatable DateRange target. -/
structure CheckedDateRangeConstructionComputation (model : FlatModel) where
  construction : CheckedDateRangeConstruction model
  target : CheckedDirectDateRange model
  declaringGroup : GroupPath
  /-- The declaring group is a representable path. Placement itself is unconstrained here — a
  construction reads two nonrepeatable endpoints, so nothing iterates and the Kernel's containment
  gate cannot fire ([checkpoint](../../docs/sources/computation-placement-and-constant-probes.md#src-fixed-target-star-placement)) — but the
  group must still be a group, and nothing else in this certificate implies it. -/
  declaringGroupValid : GroupPath.isValid declaringGroup = true
  format : DateRangeConstructionTargetFormat
  profileOwned :
    DateRangeConstructionTargetFormat.ofProfiles?
      construction.start.format target.format = some format
  /-- Neither endpoint is the target, so a plan step over the construction never reads its own target.
  The endpoints are Date fields and the target a DateRange one, so this never refuses a checked model. -/
  startNotTarget : construction.start.checked.target.id ≠ target.source.id
  finishNotTarget : construction.finish.checked.target.id ≠ target.source.id

/-- Certify one supported construction and matching DateRange target against the same checked model. -/
def elaborateDateRangeConstructionComputation
    (model : FlatModel) (declaringGroup : GroupPath) (targetField : FieldId)
    (start finish : FieldId) :
    Except DateRangeConstructionComputationElabError
      (CheckedDateRangeConstructionComputation model) := do
  let construction ← elaborateDateRangeConstruction model start finish
    |>.mapError .construction
  -- Resolved for its refusal, not its result: a repeatable target fails here as
  -- `repeatableReference`, before the direct-DateRange check would report a different class.
  let _ ← model.resolveNonrepeatableDeclarationById targetField
    |>.mapError (fun error => .target (.source error))
  let target ← elaborateDirectDateRange model targetField |>.mapError .target
  -- Validity only, not placement: the target may sit anywhere, but `[]` and an empty segment are
  -- not groups. Removing the former equality test removed the only thing that implied this.
  if hValid : GroupPath.isValid declaringGroup = true then
    match hFormat : DateRangeConstructionTargetFormat.ofProfiles?
        construction.start.format target.format with
    | some format =>
        if hStart : construction.start.checked.target.id ≠ target.source.id then
          if hFinish : construction.finish.checked.target.id ≠ target.source.id then
            pure {
              construction
              target
              declaringGroup
              declaringGroupValid := hValid
              format
              profileOwned := hFormat
              startNotTarget := hStart
              finishNotTarget := hFinish
            }
          else throw .incoherentCore
        else throw .incoherentCore
    | none =>
        throw (.endpointFormat construction.start.format construction.finish.format)
  else
    throw (.target (.source (.invalidRuleGroup declaringGroup)))

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

inductive BoundDateRangeConstructionElabError where
  | resolve (cause : ResolveError)
  | placement (cause : AddressedRepeatableTargetElabError)
  | construction (cause : DateRangeConstructionElabError)
  | target (cause : DirectDateRangeElabError)
  | profileMismatch
  deriving Repr, DecidableEq

/-- A constructor bound to a fixed or repeated target, preserving the existing endpoint and target profiles. -/
structure CheckedBoundDateRangeConstructionComputation (model : FlatModel) where
  private mk ::
  construction : CheckedDateRangeConstruction model
  target : CheckedDateRangeSource model
  format : DateRangeConstructionTargetFormat
  profileOwned : DateRangeConstructionTargetFormat.ofProfiles?
    construction.start.format target.format = some format

/-- Resolve authored endpoints at the lexical group and bind their reads at the target (spec/05, spec/09). -/
def checkBoundDateRangeConstructionComputation (model : FlatModel) (group : GroupPath)
    (targetField : FieldId) (start finish : SurfaceFieldPath) :
    Except BoundDateRangeConstructionElabError (CheckedBoundDateRangeConstructionComputation model) := do
  let declaration ← (model.lookupUniqueId targetField).mapError .resolve
  if !GroupPath.isValid group then throw (.resolve (.invalidRuleGroup group))
  if !declaration.repeatableScope.isEmpty then
    let _ ← (checkAddressedRepeatableTarget model group targetField).mapError .placement
  let start ← (model.resolveFieldDeclarationUnchecked group start).mapError .resolve
  let finish ← (model.resolveFieldDeclarationUnchecked group finish).mapError .resolve
  let construction ← (elaborateDateRangeConstructionIn model declaration.repeatableScope start.id finish.id).mapError .construction
  let target ← (elaborateDateRangeSourceIn model declaration.repeatableScope targetField).mapError .target
  match owned : DateRangeConstructionTargetFormat.ofProfiles? construction.start.format target.format with
  | none => throw .profileMismatch
  | some format => pure { construction, target, format, profileOwned := owned }

namespace CheckedBoundDateRangeConstructionComputation

def referencesField (operation : CheckedBoundDateRangeConstructionComputation model) (field : FieldId) : Bool :=
  operation.construction.start.checked.target.id == field || operation.construction.finish.checked.target.id == field

/-- Computation observes endpoint poison before empty suppression and renders through the target's own profile. -/
def evaluateWith (operation : CheckedBoundDateRangeConstructionComputation model)
    (read : FieldId → CheckedCell) : Except DateRangeConstructionComputationFault DateRangeTargetOutcome := do
  let observation ← (operation.construction.evaluateWith .computation (fun field => pure (read field))).mapError .construction
  (operation.format.evaluateComputationResult observation.asComputationResult).mapError .target

end CheckedBoundDateRangeConstructionComputation

end A12Kernel
