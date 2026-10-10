import A12Kernel.Elaboration.AddressedRepeatableTarget
import A12Kernel.Elaboration.ComputationFormalInput
import A12Kernel.Elaboration.StringComputation
import A12Kernel.Elaboration.StringComputationRunApplication
import A12Kernel.Elaboration.TokenEntityList
import A12Kernel.Semantics.FirstFilledValue

/-! # Ordinary String `FirstFilledValue` at a fixed or a repeatable target

One carrier serves both address classes. The source is the shared String/Enumeration entity list,
its shape asked against the target's group, so every repeatable level an operand leaves unstarred is
bound by the target's rows ([`spec/09`](../../spec/09-computations.md) §1). A fixed target runs once,
at its single instance, the empty environment; a repeatable one runs at every instantiated row of its
scope and clears an over-limit row. The scan is the kind-neutral computation walk
`scanComputationFirstFilledSelections`, here over token cells.

Placement stays split, as measured: a repeatable target must lie at or below the declaring group and
must not be an index field, while a fixed target is unrestricted until an operand derives iteration
([`spec/09`](../../spec/09-computations.md) §1).
-/

namespace A12Kernel


namespace CheckedTokenEntityOperand

/-- The declarations one slot reads: a field's, a star's, or every slot of a group's expansion. -/
def declarations : CheckedTokenEntityOperand model → List FlatFieldDecl
  | .field source => [source.declaration]
  | .star source => [source.source.declaration]
  | .selected source => source.slots.map (·.declaration)
  | .group source => source.slots.map (·.declaration)

/-- Resolve one reached slot at the scan's environment `outer`: a field read at it, a star's
in-capacity rows below it, filtered or not, or a selected/group extent in the shared walk's order. -/
def computationSelection (document : Document) (outer : Env)
    (read : Env → FieldId → CheckedCell)
    (world : Option World := none)
    (selectedRead : CheckedSelectedTokenEntity model → Except StarAddressingError (ResolvedValueListSide .token) :=
      fun source => .error (.unsupportedGroupOperand source.path))
    (filterStoredText : Env → FieldId → Option String := fun _ _ => none)
    (filterNumberText : Env → FieldId → Option String := fun _ _ => none) :
    CheckedTokenEntityOperand model →
      Except StarAddressingError (FirstFilledComputationSelection .token)
  | .selected source => (.side ·) <$> selectedRead source
  | .field source => pure (.cell (source.valueListCellAt .computation (read outer)))
  | .star source => do
      let resolved ← source.source.path.resolveInCapacity document outer
      let classify := source.valueListCellAt .computation read
      match source.filter with
      | none => pure (.rows resolved.environments resolved.domain.hasOpenTail classify)
      | some having => do
          let candidates ← model.filterEnvironments source.source.path
            (document.filterRows.getD document.instantiatedRows) outer
          let read := model.filterRead document read
          pure (.filtered having.condition
            (({ read, world, storedText := filterStoredText, numberText := filterNumberText } : CorrelationContext).withModelComputationGroups model document) candidates
            resolved.domain.hasOpenTail (source.valueListCellAt .computation read))
  | .group source => (.side ·) <$> source.resolvedSideIn .computation document outer read

end CheckedTokenEntityOperand

inductive StringFirstFilledComputationElabError where
  | target (cause : ResolveError)
  /-- A repeatable target's placement, which the shared repeatable-target certificate owns. -/
  | placement (cause : AddressedRepeatableTargetElabError)
  | targetNotOrdinaryString (path : List String)
  | source (cause : TokenEntityElabError)
  | sourceNotOrdinaryString (path : List String)
  /-- A source naming the target itself. -/
  | targetSelfReference (path : List String)
  | declaringGroupInvalid (group : GroupPath)
  deriving Repr, DecidableEq

/-- Project the source's shape refusals, whose classes belong to the path rather than the carrier: an
unstarred level the target does not bind draws its class on every carrier measured, the String
`FirstFilledValue` computation among them
([checkpoint](../../docs/sources/group-list-and-capacity-probes.md#src-computation-star-binding-gate)),
and a source naming the target the target-read class, measured on this carrier
([checkpoint](../../docs/sources/diagnostic-class-vocabulary-and-sweeps.md#src-computation-self-read-sweep),
row `F01`). The other refusals are unmeasured here and claim no class. -/
def StringFirstFilledComputationElabError.diagnostic? :
    StringFirstFilledComputationElabError → Option KernelStaticDiagnostic
  | .source (.shape cause) => cause.diagnostic?
  | .targetSelfReference _ => some .errorReferenceToCalculatedField
  | .target _ | .placement _ | .targetNotOrdinaryString _ | .source _
  | .sourceNotOrdinaryString _ | .declaringGroupInvalid _ => none

/-- One ordinary String target, fixed or repeatable, and one ordinary String entity-list source
bound by the target's rows, certified against the same model. -/
structure CheckedStringFirstFilledComputation (model : FlatModel) where
  private mk ::
  targetField : FieldId
  target : FlatFieldDecl
  targetOwned : model.lookupUniqueId targetField = .ok target
  source : CheckedTokenEntitySource model
  /-- The group the computation is declared in, which a fixed target need not lie in. -/
  declaringGroup : GroupPath
  declaringGroupValid : GroupPath.isValid declaringGroup = true
  /-- A repeatable target lies at or below the declaring group and is no index field. -/
  targetPlaced : (target.repeatableScope.isEmpty ||
    (GroupPath.isPrefixOf declaringGroup target.groupPath && !model.isIndexField targetField)) = true
  targetOrdinary : target.isOrdinaryStringComputationCarrier = true
  sourceOrdinary :
    source.operands.all (·.declarations.all (·.isOrdinaryStringComputationCarrier)) = true
  excludesTarget : source.referencesField targetField (fun having _ => having.forbidsTarget targetField) = false

/-- Check the target's placement and carrier, then the source against the target's group. -/
def checkStringFirstFilledComputation
    (model : FlatModel) (declaringGroup : GroupPath) (targetField : FieldId)
    (authored : SurfaceTokenEntitySource) :
    Except StringFirstFilledComputationElabError (CheckedStringFirstFilledComputation model) := do
  match hOwned : model.lookupUniqueId targetField with
  | .error cause => throw (.target cause)
  | .ok target =>
    if !target.repeatableScope.isEmpty then
      discard <| (checkAddressedRepeatableTarget model declaringGroup targetField).mapError .placement
    if hTarget : target.isOrdinaryStringComputationCarrier = true then
      let source ← (elaborateTokenEntitySource model declaringGroup authored
          (fixedTargetGroup? := some target.groupPath)).mapError .source
      if hSource : source.operands.all
          (·.declarations.all (·.isOrdinaryStringComputationCarrier)) = true then
        if hExcludes : source.referencesField targetField (fun having _ => having.forbidsTarget targetField) = false then
          if hValid : GroupPath.isValid declaringGroup = true then
            if hPlaced : (target.repeatableScope.isEmpty || (GroupPath.isPrefixOf declaringGroup
                target.groupPath && !model.isIndexField targetField)) = true then
              pure {
                targetField, target, source, declaringGroup
                targetOwned := hOwned
                declaringGroupValid := hValid
                targetPlaced := hPlaced
                targetOrdinary := hTarget
                sourceOrdinary := hSource
                excludesTarget := hExcludes }
            -- The repeatable-target certificate above already refused every placement failing here.
            else throw (.placement (.targetOutsideDeclaringGroup target.path declaringGroup))
          else throw (.declaringGroupInvalid declaringGroup)
        else throw (.targetSelfReference target.path)
      else
        let other := ((source.operands.flatMap (·.declarations)).find?
          (!·.isOrdinaryStringComputationCarrier)).getD target
        throw (.sourceNotOrdinaryString other.path)
    else throw (.targetNotOrdinaryString target.path)

namespace TokenComputationResult

/-- Convert selection into the ordinary String root-store domain before target policy runs. -/
def asStringStore : TokenComputationResult → StringStore
  | .value token =>
      if nonempty : token ≠ "" then .produced { text := token, nonempty }
      else .noValue
  | .noValue => .noValue
  | .poison cause => .poison cause

end TokenComputationResult

inductive StringFirstFilledComputationFault where
  | targetPatternUnavailable (field : FieldId)
  | targetRows (cause : ActualRowEnvironmentError)
  | targetEnvironment (cause : EnvBindingError)
  | source (cause : StarAddressingError)
  deriving Repr, DecidableEq

/-- One target instance's outcome at its exact address before source-relative classification. -/
structure StringFirstFilledComputationOutcome where
  targetField : CellAddr
  outcome : StringTargetOutcome
  deriving Repr, DecidableEq

/-- One checked String first-filled result retaining its admitted operation. -/
structure StringFirstFilledComputationRunView (model : FlatModel) (ResidualMessage : Type) where
  private mk ::
  operation : CheckedStringFirstFilledComputation model
  string : StringComputationRunView ResidualMessage CellAddr

namespace CheckedStringFirstFilledComputation

def referencesWith (operation : CheckedStringFirstFilledComputation model) (field : FieldId)
    (filterReads : CorrelatedHaving → Bool) : Bool :=
  operation.source.referencesField field (fun having _ => filterReads having)

def referencesField (operation : CheckedStringFirstFilledComputation model) (field : FieldId) : Bool :=
  operation.referencesWith field (·.referencesField field)

/-- Scan the source at one target instance's environment, then run the exact declaration-owned
String target policy and the target's prepared matcher. -/
def evaluateAt (operation : CheckedStringFirstFilledComputation model)
    (matcher : Option (String → Bool)) (input : CheckedDocument model)
    (read : CellAddr → Except CheckedDocumentError CheckedCell) (environment : Env)
    (world : Option World := none) :
    Except StringFirstFilledComputationFault StringFirstFilledComputationOutcome := do
  let targetPath ← environment.pathForScope operation.target.repeatableScope
    |>.mapError .targetEnvironment
  let selected ← scanComputationFirstFilledSelections environment
    (fun
      | .calendarUnavailable => .unsupportedDateCalendar
      | .valueFailure => .temporalValueFailure
      | .worldUnavailable => .worldUnavailable
      | .typeValidityValueFailure => .typeValidityValueFailure
      | .stringExpressionUnavailable => .stringExpressionUnavailable
      | .storedTextUnavailable fieldId => .storedTextUnavailable fieldId
      | .groupUnavailable path => .unsupportedGroupOperand path)
      (·.computationSelection (world := world) (filterStoredText := input.storedTextWithRead read) input.readDocument environment (input.computationCellAt read)
        (selectedRead := fun source => source.sideWith .computation input.readDocument environment
          (input.computationCellAt read environment) (input.storedTextWithRead read environment) (input.computationCellAt read)
          (input.resolveSemanticIndexColumnWith read) |>.mapError (fun _ => .unsupportedGroupOperand source.path)))
      operation.source.operands {}
    |>.mapError .source
  let result : FirstFilledTokenResult := match selected with
    | .inl _ => .noValue
    | .inr result => result.asToken
  pure {
    targetField := { field := operation.targetField, path := targetPath }
    outcome := operation.target.stringPolicy.checkTargetWithPattern matcher
      result.asComputationResult.asStringStore }

/-- The no-value outcome an over-limit target row takes instead of a scan, at its exact address, so
the application projection clears it. -/
def clearedAt (operation : CheckedStringFirstFilledComputation model) (environment : Env) :
    Except StringFirstFilledComputationFault StringFirstFilledComputationOutcome := do
  let targetPath ← environment.pathForScope operation.target.repeatableScope
    |>.mapError .targetEnvironment
  pure { targetField := { field := operation.targetField, path := targetPath }, outcome := .noValue }

/-- Run at the fixed target's single instance, or at every instantiated row of a repeatable target's
scope with a clear at each over-limit row, through a caller-supplied exact-address view. -/
def executeWithMatcher (operation : CheckedStringFirstFilledComputation model)
    (matcher : Option (String → Bool)) (input : CheckedDocument model)
    (read : CellAddr → Except CheckedDocumentError CheckedCell)
    (world : Option World := none) :
    Except StringFirstFilledComputationFault (List StringFirstFilledComputationOutcome) :=
  input.computationTargetOutcomes operation.target.repeatableScope .targetRows operation.clearedAt
    (operation.evaluateAt (world := world) matcher input read)

/-- Run with the target's prepared matcher, which must be present before any instance runs. -/
def executeWithRead (operation : CheckedStringFirstFilledComputation model)
    (patterns : PreparedFlatStringPatterns model compilePattern) (input : CheckedDocument model)
    (read : CellAddr → Except CheckedDocumentError CheckedCell)
    (world : Option World := none) :
    Except StringFirstFilledComputationFault (List StringFirstFilledComputationOutcome) := do
  let matcher ← match patterns.targetMatcher? operation.targetField with
    | some matcher => pure matcher
    | none => throw (.targetPatternUnavailable operation.targetField)
  operation.executeWithMatcher (world := world) matcher input read

def execute (operation : CheckedStringFirstFilledComputation model)
    (patterns : PreparedFlatStringPatterns model compilePattern) (input : CheckedDocument model)
    (world : Option World := none) :
    Except StringFirstFilledComputationFault (List StringFirstFilledComputationOutcome) :=
  operation.executeWithRead (world := world) patterns input input.read

/-- Classify caller-view outcomes against the immutable source target at the same addresses. -/
def executeResultWithRead (operation : CheckedStringFirstFilledComputation model)
    (patterns : PreparedFlatStringPatterns model compilePattern) (input : CheckedDocument model)
    (read : CellAddr → Except CheckedDocumentError CheckedCell)
    (residualMessages : List ResidualMessage)
    (world : Option World := none) :
    Except StringFirstFilledComputationFault
      (StringFirstFilledComputationRunView model ResidualMessage) := do
  let outcomes ← operation.executeWithRead (world := world) patterns input read
  pure {
    operation
    string := StringComputationRunView.fromSourcedOutcomes residualMessages
      (outcomes.map fun entry => {
        targetField := entry.targetField
        outcome := entry.outcome
        source := input.sourceStringTargetStateAt entry.targetField }) }

def executeResult (operation : CheckedStringFirstFilledComputation model)
    (patterns : PreparedFlatStringPatterns model compilePattern) (input : CheckedDocument model)
    (residualMessages : List ResidualMessage)
    (world : Option World := none) :
    Except StringFirstFilledComputationFault
      (StringFirstFilledComputationRunView model ResidualMessage) :=
  operation.executeResultWithRead (world := world) patterns input input.read residualMessages

end CheckedStringFirstFilledComputation

namespace StringFirstFilledComputationRunView

/-- Apply retained exact-address actions to a separate same-model destination without reclassifying them. -/
def applyToChecked (view : StringFirstFilledComputationRunView model ResidualMessage)
    (destination : CheckedDocument model) :
    Except (StringComputationRunView.StringComputationRunApplicationError CellAddr)
      (StringComputationDestination CellAddr) :=
  view.string.applyTo destination.sourceStringTargetStateAt

end StringFirstFilledComputationRunView

/-- Failure while composing selected formal-input preparation with String `FirstFilledValue`. -/
inductive StringFirstFilledCheckedResultFault where
  | formalInput (cause : ComputationFormalInputPlanError)
  | preliminary (cause : CheckedIndexPreliminaryError)
  | execution (formalErrorsInOperands : List ComputationFormalInputFinding)
      (cause : StringFirstFilledComputationFault)
  deriving Repr, DecidableEq

namespace CheckedStringFirstFilledComputation

/-- Bind every source declaration and the computed target to the shared eager inventory. -/
def formalInputPlan (operation : CheckedStringFirstFilledComputation model) :
    Except ComputationFormalInputPlanError (CheckedComputationFormalInputPlan model) :=
  checkImplicitGuardFormalInputPlan model
    ((operation.source.operands.flatMap (·.declarations)).map (·.id)) [operation.targetField]

/-- Prepare the selected sources once, retain every eager finding, and run lazily through the
prepared read. -/
def executeResultWithFormalInputs (operation : CheckedStringFirstFilledComputation model)
    (patterns : PreparedFlatStringPatterns model compilePattern) (input : CheckedDocument model)
    (world : Option World := none) :
    Except StringFirstFilledCheckedResultFault
      (StringFirstFilledComputationRunView model ComputationFormalInputFinding) := do
  let plan ← operation.formalInputPlan |>.mapError .formalInput
  let prepared ← plan.prepare input |>.mapError .preliminary
  match operation.executeResultWithRead (world := world) patterns input prepared.preliminary.readComputation
      prepared.formalErrorsInOperands with
  | .error cause => .error (.execution prepared.formalErrorsInOperands cause)
  | .ok result => .ok result

end CheckedStringFirstFilledComputation

end A12Kernel
