import A12Kernel.Elaboration.DateRangeBound
import A12Kernel.Elaboration.TemporalTargetPolicy
import A12Kernel.Elaboration.DateRangeInput
import A12Kernel.Semantics.DateRangeConstruction
import A12Kernel.Elaboration.CheckedStarDocument

/-! # Checked DateRange construction comparison

The endpoint certificate retains declaration precision, model-zone interpretation and optional checked semantic-index selection. Direct and selected sources share positional completion and component admission; comparisons and computation constructors supply their phase and current read context. Selected payload rows remain distinct from the caller's binding scope. The fixed direct APIs retain their original input and result boundaries.
-/

namespace A12Kernel

namespace DateRangeEndpointFormat

/-- Match the construction's available component identity to the stored declaration profile.
Lexical spelling does not enter it, so both full-Date formats, both month-only spellings, and
both day-and-month spellings each accept a construction of their own component set. -/
def matchesStoredInput (endpoint : DateRangeEndpointFormat)
    (stored : DateRangeInputFormat) : Bool :=
  endpoint.components == stored.components

end DateRangeEndpointFormat

/-- One construction endpoint, admitted by its declared **format** alone.

    The endpoint is an operand position — its refusal reports the operand class below, not a target
    class — so it follows the operand rule rather than the target one: every temporal operand gate
    reads the declared format and never the declared kind
    ([checkpoint](../../docs/sources/computation-placement-and-constant-probes.md#src-temporal-difference-gates-read-the-format)).
    The format test already admits only Date-shaped formats, which is why the retired kind conjunct
    changed nothing except to refuse the cross-kind declaration the Kernel accepts. -/
structure CheckedDateRangeEndpoint (model : FlatModel) where
  checked : CheckedTemporalTargetPolicy model
  format : DateRangeEndpointFormat
  profile : ModelZone.ConcreteProfile
  formatMatches : DateRangeEndpointFormat.ofPolicy? model.baseYear checked.policy = some format
  profileMatches : ModelZone.ConcreteProfile.ofId? checked.timeZoneId = some profile
  selection? : Option { source : CheckedSemanticIndexSource model //
    source.targetDeclaration.id = checked.target.id } := none

inductive DateRangeEndpointElabError where
  | targetPolicy (cause : TemporalTargetElabError)
  | unsupportedPolicy (target : FieldId) (mode : TemporalPartialMode)
      (format : String)
  | unsupportedZone (zoneId : String)
  | selection (cause : SemanticIndexElabError)
  deriving Repr, DecidableEq

namespace DateRangeEndpointElabError

/-- The Kernel diagnostic one refused construction endpoint reports. Every operand whose declared
**format** is not a Date-shaped one — a clock, a DateTime, a DateRange, and a partial Date outside
the admitted fragment set — reports the one wrong-format class, so nothing about the operand's
declaration is recoverable from the code. A repeatable operand reached from outside its group
reports the missing-wildcard class instead. The remaining causes are local ingestion insufficiency
with no measured counterpart, and a **starred** operand is not expressible at this boundary at all,
because it resolves a field id rather than an authored path. -/
def diagnostic? : DateRangeEndpointElabError → Option KernelStaticDiagnostic
  | .unsupportedPolicy _ _ _ => some .wrongDateFormatForOp
  | .targetPolicy (.targetNotTemporal _ _) => some .wrongDateFormatForOp
  | .targetPolicy (.resolve error) => error.diagnostic?
  | .selection error => error.diagnostic?
  | .targetPolicy _ | .unsupportedZone _ => none

end DateRangeEndpointElabError

/-- Resolve one exact-or-yearless nonrepeatable endpoint profile without widening the scalar Date target owner. -/
def elaborateDateRangeEndpointIn (model : FlatModel)
    (scope : List RepeatableLevel) (field : FieldId) :
    Except DateRangeEndpointElabError (CheckedDateRangeEndpoint model) := do
  let checked ← elaborateTemporalTargetPolicyIn model scope field
    |>.mapError .targetPolicy
  match hFormat : DateRangeEndpointFormat.ofPolicy? model.baseYear checked.policy with
  | none => throw (.unsupportedPolicy field checked.policy.partialMode checked.policy.format)
  | some format =>
      match hProfile : ModelZone.ConcreteProfile.ofId? checked.timeZoneId with
      | none => throw (.unsupportedZone checked.timeZoneId)
      | some profile => pure {
          checked
          format
          profile
          formatMatches := hFormat
          profileMatches := hProfile }

/-- The scalar instance: an endpoint read where the reading rule iterates no level. -/
def elaborateDateRangeEndpoint (model : FlatModel) (field : FieldId) :
    Except DateRangeEndpointElabError (CheckedDateRangeEndpoint model) :=
  elaborateDateRangeEndpointIn model [] field

inductive SurfaceDateRangeEndpoint where
  | field (path : SurfaceFieldPath)
  | indexed (source : SurfaceSemanticIndex)

/-- Selection establishes the endpoint row before its declaration supplies precision and zone
(spec/05 §8; spec/08 §4.2). The selected payload does not bind the caller to that row. -/
def elaborateDateRangeEndpointSource (model : FlatModel) (group : GroupPath)
    (scope : List RepeatableLevel) (source : SurfaceDateRangeEndpoint) :
    Except DateRangeEndpointElabError (CheckedDateRangeEndpoint model) := do
  match source with
  | .field path =>
      let declaration ← (model.resolveFieldDeclarationUnchecked group path).mapError
        (DateRangeEndpointElabError.targetPolicy ∘ TemporalTargetElabError.resolve)
      elaborateDateRangeEndpointIn model scope declaration.id
  | .indexed authored =>
      let selection ← (elaborateSemanticIndexSource model group authored (some scope)).mapError .selection
      let endpoint ← elaborateDateRangeEndpointIn model selection.targetDeclaration.repeatableScope
        selection.targetDeclaration.id
      if same : selection.targetDeclaration.id = endpoint.checked.target.id then
        pure { endpoint with selection? := some ⟨selection, same⟩ }
      else throw (.selection .incoherentCore)

def CheckedDateRangeEndpoint.referencesField (source : CheckedDateRangeEndpoint model)
    (field : FieldId) : Bool :=
  match source.selection? with
  | none => source.checked.target.id == field
  | some selection => selection.val.referencesField field

def CheckedDateRangeEndpoint.referencesErrorField (source : CheckedDateRangeEndpoint model)
    (field : FieldId) : Bool :=
  source.checked.target.id == field || source.selection?.any fun selection =>
    match selection.val.key with
    | .literal .. => false
    | .field declaration => declaration.id == field

structure CheckedDateRangeConstruction (model : FlatModel) where
  start : CheckedDateRangeEndpoint model
  finish : CheckedDateRangeEndpoint model
  componentsMatch : start.format.sameComponents finish.format = true

inductive DateRangeConstructionElabError where
  | start (cause : DateRangeEndpointElabError)
  | finish (cause : DateRangeEndpointElabError)
  | componentMismatch (start finish : DateRangeEndpointFormat)
  deriving Repr, DecidableEq

namespace DateRangeConstructionElabError

/-- Endpoint refusals keep their own diagnostic, and a pair whose component sets disagree reports
the same wrong-format class as a wrong-kind operand, so that one code covers both the operand and
the pair. -/
def diagnostic? : DateRangeConstructionElabError → Option KernelStaticDiagnostic
  | .start cause | .finish cause => cause.diagnostic?
  | .componentMismatch _ _ => some .wrongDateFormatForOp

end DateRangeConstructionElabError

def checkDateRangeConstructionEndpoints (start finish : CheckedDateRangeEndpoint model) :
    Except DateRangeConstructionElabError (CheckedDateRangeConstruction model) :=
  if same : start.format.sameComponents finish.format then
    pure { start, finish, componentsMatch := same }
  else throw (.componentMismatch start.format finish.format)

/-- Certify one pair of construction endpoints once for every checked comparison consumer. `scope`
is the reading rule's iteration scope, so an endpoint inside a level the rule iterates is admitted
and every other gate stays unchanged. -/
def elaborateDateRangeConstructionIn (model : FlatModel)
    (scope : List RepeatableLevel) (start finish : FieldId) :
    Except DateRangeConstructionElabError
      (CheckedDateRangeConstruction model) := do
  let checkedStart ← elaborateDateRangeEndpointIn model scope start
    |>.mapError .start
  let checkedFinish ← elaborateDateRangeEndpointIn model scope finish
    |>.mapError .finish
  checkDateRangeConstructionEndpoints checkedStart checkedFinish

/-- The scalar instance: a construction read where the reading rule iterates no level. -/
def elaborateDateRangeConstruction (model : FlatModel)
    (start finish : FieldId) :
    Except DateRangeConstructionElabError
      (CheckedDateRangeConstruction model) :=
  elaborateDateRangeConstructionIn model [] start finish

inductive DateRangeConstructionComparisonElabError where
  | left (cause : DateRangeConstructionElabError)
  | right (cause : DateRangeConstructionElabError)
  | componentMismatch (left right : DateRangeEndpointFormat)
  deriving Repr, DecidableEq

namespace DateRangeConstructionComparisonElabError

/-- Each side keeps its own construction diagnostic, and a pair whose component sets disagree reports
the wrong-format class the endpoint refusals already use, so one code covers the operand, the
construction, and the pair. -/
def diagnostic? :
    DateRangeConstructionComparisonElabError → Option KernelStaticDiagnostic
  | .left cause | .right cause => cause.diagnostic?
  | .componentMismatch _ _ => some .wrongDateFormatForOp

end DateRangeConstructionComparisonElabError

structure CheckedDateRangeConstructionComparison (model : FlatModel) where
  left : CheckedDateRangeConstruction model
  right : CheckedDateRangeConstruction model
  comparison : EqualityOp
  componentsMatch : left.start.format.sameComponents right.start.format = true

/-- Certify all four endpoint declarations and the cross-construction component invariant while
retaining the authored comparison. `scope` is the reading rule's iteration scope, so an endpoint
inside a level the rule iterates is admitted on either side. -/
def elaborateDateRangeConstructionComparisonIn (model : FlatModel)
    (scope : List RepeatableLevel)
    (leftStart leftFinish rightStart rightFinish : FieldId)
    (comparison : EqualityOp) :
    Except DateRangeConstructionComparisonElabError
      (CheckedDateRangeConstructionComparison model) := do
  let left ← elaborateDateRangeConstructionIn model scope leftStart leftFinish
    |>.mapError .left
  let right ← elaborateDateRangeConstructionIn model scope rightStart rightFinish
    |>.mapError .right
  if hComponents : left.start.format.sameComponents right.start.format then
    pure {
      left
      right
      comparison
      componentsMatch := hComponents }
  else
    throw (.componentMismatch left.start.format right.start.format)

/-- The scalar instance: a comparison read where the reading rule iterates no level. -/
def elaborateDateRangeConstructionComparison (model : FlatModel)
    (leftStart leftFinish rightStart rightFinish : FieldId)
    (comparison : EqualityOp) :
    Except DateRangeConstructionComparisonElabError
      (CheckedDateRangeConstructionComparison model) :=
  elaborateDateRangeConstructionComparisonIn model [] leftStart leftFinish
    rightStart rightFinish comparison

/-- Structural failure outside the phase-sensitive endpoint observations. -/
inductive DateRangeConstructionFault where
  | document (cause : CheckedDocumentError)
  | endpointValueKind (source : FieldId)
  | endpointDateUnavailable (source : FieldId) (value : DateValue)
  | addressing (cause : CheckedAddressingError)
  deriving Repr, DecidableEq

namespace CheckedDateRangeConstruction

end CheckedDateRangeConstruction

namespace DateRangeEndpointFormat

/-- Direct checked documents and correlated operands share positional completion (spec/05 §8). -/
def evaluateObservation (format : DateRangeEndpointFormat)
    (profile : ModelZone.ConcreteProfile) (field : FieldId)
    (bound : DateRangeBound) (observation : CellObservation) :
    Except DateRangeConstructionFault (CellObservation DateRangeConstructionEndpointValue) :=
  format.evaluateObservationWith profile field .endpointValueKind .endpointDateUnavailable bound observation

end DateRangeEndpointFormat

namespace CheckedDateRangeConstruction

private def evaluateEndpoint (source : CheckedDateRangeEndpoint model)
    (bound : DateRangeBound) (phase : Phase)
    (read : FieldId → Except DateRangeConstructionFault CheckedCell)
    (select : CheckedSemanticIndexSource model → Except DateRangeConstructionFault CellObservation) :
    Except DateRangeConstructionFault
      (CellObservation DateRangeConstructionEndpointValue) := do
  let field := source.checked.target.id
  let observation ← match source.selection? with
    | none => observeCell phase <$> read field
    | some selection => select selection.val
  source.format.evaluateObservation source.profile field bound observation

/-- Observe both endpoints from cells already read at the consuming row. A payload the endpoint
projection rejects collapses to UNKNOWN rather than claiming a fault channel a row-reading consumer
does not own; the endpoint certificates' kind, profile, and format gates make that collapse
unreachable. -/
def observeAt (construction : CheckedDateRangeConstruction model)
    (startCell finishCell : CheckedCell) : DateRangeConstructionObservation :=
  let observe (endpoint : CheckedDateRangeEndpoint model)
      (bound : DateRangeBound) (cell : CheckedCell) :
      CellObservation DateRangeConstructionEndpointValue :=
    match endpoint.format.evaluateObservation endpoint.profile
        endpoint.checked.target.id bound (observeCell .validation cell) with
    | .ok observed => observed
    | .error _ => .unknown .malformed
  { start := observe construction.start .start startCell
    finish := observe construction.finish .finish finishCell }

/-- Fixed and bound consumers share phase-sensitive, start-before-finish completion (spec/05). -/
def evaluateWith (construction : CheckedDateRangeConstruction model) (phase : Phase)
    (read : FieldId → Except DateRangeConstructionFault CheckedCell)
    (select : CheckedSemanticIndexSource model → Except DateRangeConstructionFault CellObservation :=
      fun source => throw (.addressing (.checkedDocumentRequired source.group.path))) :
    Except DateRangeConstructionFault DateRangeConstructionObservation := do
  let start ← evaluateEndpoint construction.start .start phase read select
  let finish ← evaluateEndpoint construction.finish .finish phase read select
  pure { start, finish }

def evaluateInContext (construction : CheckedDateRangeConstruction model) (phase : Phase)
    (context : ScalarComputationContext) :
    Except DateRangeConstructionFault DateRangeConstructionObservation :=
  construction.evaluateWith phase (fun field => pure (context.read field)) fun source =>
    (source.observeColumnWith phase context.semanticIndexColumnReader context.row
      context.read context.storedText).mapError .addressing

/-- Immutable readers preserve the selected row and phase while direct endpoints use the caller's address. -/
def evaluateAt (construction : CheckedDateRangeConstruction model)
    (phase : Phase) (input : CheckedDocument model) (outer : Env) :
    Except DateRangeConstructionFault DateRangeConstructionObservation :=
  let read := if phase == .validation then input.fullValidationRead else input.read
  construction.evaluateWith phase
    (fun field => (input.checkedCellWithRead read outer field).mapError .addressing)
    (fun source => (source.observeColumnWith phase (input.resolveSemanticIndexColumnWith read)
      outer (input.computationCellAt read outer) (input.storedTextWithRead read outer)).mapError .addressing)

/-- Read each certified endpoint once from one immutable checked document. -/
def evaluate (construction : CheckedDateRangeConstruction model)
    (phase : Phase) (input : CheckedDocument model) :
    Except DateRangeConstructionFault DateRangeConstructionObservation :=
  let context := input.computationContextAt []
  construction.evaluateWith phase
    (fun field => (input.read { field, path := [] }).mapError .document)
    (fun source => (source.observeColumnWith phase (input.resolveSemanticIndexColumnWith input.read)
      [] context.read context.storedText).mapError .addressing)

end CheckedDateRangeConstruction

/-- Compare two already-read construction observations. The read is deliberately not part of this
step, so a consumer reading its endpoints at a rule's row reaches the same comparison as the
document-reading path. -/
def CheckedDateRangeConstructionComparison.verdictOf
    (checked : CheckedDateRangeConstructionComparison model)
    (left right : DateRangeConstructionObservation) : Verdict :=
  checked.comparison.evalDateRangeCellValues left.comparisonOperand
    right.comparisonOperand

/-- Rich checked result retaining both constructions beside their projected verdict. -/
structure DateRangeConstructionComparisonResult where
  left : DateRangeConstructionObservation
  right : DateRangeConstructionObservation
  verdict : Verdict
  deriving Repr, DecidableEq

namespace CheckedDateRangeConstructionComparison

/-- Compare internally read observations without discarding endpoint identity or availability. -/
private def evaluateObserved (operation : CheckedDateRangeConstructionComparison model)
    (left right : DateRangeConstructionObservation) :
    DateRangeConstructionComparisonResult := {
  left
  right
  verdict := operation.comparison.evalDateRangeCellValues
    left.comparisonOperand right.comparisonOperand }

/-- Read both checked constructions in validation phase from the same immutable document and evaluate their exact-or-yearless endpoint identity. -/
def evaluate (operation : CheckedDateRangeConstructionComparison model)
    (input : CheckedDocument model) :
    Except DateRangeConstructionFault
      DateRangeConstructionComparisonResult := do
  let left ← operation.left.evaluate .validation input
  let right ← operation.right.evaluate .validation input
  pure (operation.evaluateObserved left right)

end CheckedDateRangeConstructionComparison

/-! ## Construction-versus-stored execution -/

inductive DateRangeConstructionStoredComparisonElabError where
  | construction (cause : DateRangeConstructionElabError)
  | stored (cause : DirectDateRangeElabError)
  | componentMismatch (construction : DateRangeEndpointFormat)
      (stored : DateRangeInputFormat)
  deriving Repr, DecidableEq

/-- One construction and one direct stored DateRange, retaining their authored order. -/
structure CheckedDateRangeConstructionStoredComparison (model : FlatModel) where
  construction : CheckedDateRangeConstruction model
  stored : CheckedDirectDateRange model
  position : DateRangeConstructionPosition
  comparison : EqualityOp
  componentsMatch : construction.start.format.matchesStoredInput stored.format = true

/-- Certify matching full-Date, year-bearing, Base-Year-resolved, or yearless mixed operands in authored order without introducing a second source or comparison representation. -/
def elaborateDateRangeConstructionStoredComparison (model : FlatModel)
    (start finish stored : FieldId) (position : DateRangeConstructionPosition)
    (comparison : EqualityOp) :
    Except DateRangeConstructionStoredComparisonElabError
      (CheckedDateRangeConstructionStoredComparison model) :=
  match position with
  | .left => do
      let construction ← elaborateDateRangeConstruction model start finish
        |>.mapError .construction
      let stored ← elaborateDirectDateRange model stored |>.mapError .stored
      if hComponents : construction.start.format.matchesStoredInput stored.format then
        pure {
          construction
          stored
          position
          comparison
          componentsMatch := hComponents }
      else
        throw (.componentMismatch construction.start.format stored.format)
  | .right => do
      let stored ← elaborateDirectDateRange model stored |>.mapError .stored
      let construction ← elaborateDateRangeConstruction model start finish
        |>.mapError .construction
      if hComponents : construction.start.format.matchesStoredInput stored.format then
        pure {
          construction
          stored
          position
          comparison
          componentsMatch := hComponents }
      else
        throw (.componentMismatch construction.start.format stored.format)

inductive DateRangeConstructionStoredComparisonFault where
  | construction (cause : DateRangeConstructionFault)
  | stored (cause : DirectDateRangeFault)
  deriving Repr, DecidableEq

/-- Rich mixed result retaining authored position and both exact-or-yearless operand observations. -/
structure DateRangeConstructionStoredComparisonResult where
  construction : DateRangeConstructionObservation
  stored : CellObservation DateRangeCellValue
  position : DateRangeConstructionPosition
  verdict : Verdict
  deriving Repr, DecidableEq

namespace CheckedDateRangeConstructionStoredComparison

/-- Compare already-read mixed observations through the shared exact-or-yearless equality seam. The
read is deliberately not part of this step, so a consumer that reads its operands at a rule's row
reaches the same comparison as the document-reading path below. -/
def evaluateObserved
    (operation : CheckedDateRangeConstructionStoredComparison model)
    (construction : DateRangeConstructionObservation)
    (stored : CellObservation DateRangeCellValue) :
    DateRangeConstructionStoredComparisonResult := {
  construction
  stored
  position := operation.position
  verdict := match operation.position with
    | .left => operation.comparison.evalDateRangeCellValues
        construction.comparisonOperand stored.asValidationSimpleOperand
    | .right => operation.comparison.evalDateRangeCellValues
        stored.asValidationSimpleOperand construction.comparisonOperand }

/-- Read both operands from one immutable document in authored order, preserving every observation beside the verdict. -/
def evaluate (operation : CheckedDateRangeConstructionStoredComparison model)
    (input : CheckedDocument model) :
    Except DateRangeConstructionStoredComparisonFault
      DateRangeConstructionStoredComparisonResult :=
  match operation.position with
  | .left => do
      let construction ← operation.construction.evaluate .validation input
        |>.mapError .construction
      let stored ← operation.stored.evaluate .validation input
        |>.mapError .stored
      pure (operation.evaluateObserved construction stored)
  | .right => do
      let stored ← operation.stored.evaluate .validation input
        |>.mapError .stored
      let construction ← operation.construction.evaluate .validation input
        |>.mapError .construction
      pure (operation.evaluateObserved construction stored)

end CheckedDateRangeConstructionStoredComparison

end A12Kernel
