import A12Kernel.Elaboration.StringContext
import A12Kernel.Elaboration.ValidationCondition
import A12Kernel.Elaboration.ValidationCondition.ErrorReferences
import A12Kernel.Elaboration.ValidationCondition.ErrorSelection
import A12Kernel.Elaboration.ValidationRule.AssemblyError
import A12Kernel.Elaboration.CheckedIndexPreliminary
import A12Kernel.Elaboration.CheckedStarDocument
import A12Kernel.Elaboration.CustomValidationInvocation
import A12Kernel.Semantics.ValidationRule

/-! # Checked assembly for resolved validation rules

This boundary consumes an existing checked flat or mixed condition and a resolved error-field ID. Surface rule syntax and authored message templates remain outside it.
-/

namespace A12Kernel

/-- A checked mixed rule cannot be evaluated from a scalar context when its condition retains an addressed source. This is missing execution context, not a semantic validation result. -/
inductive ValidationEvaluationError where
  | addressedContextRequired
  deriving Repr, DecidableEq

/-- Structural failures from checked ordinary repeatable rule execution remain outside semantic UNKNOWN. -/
inductive OrdinaryRepeatableRuleEvaluationError where
  | missingIterationScope
  | incoherentIterationScope (scope : List RepeatableLevel)
  | unsupportedCondition
  | incoherentRow (row : RowAddr)
  | addressing (error : CheckedAddressingError)
  | conditionAddressing (error : CheckedAddressingError)
  | preliminary (error : CheckedIndexPreliminaryError)
  | messageCache (error : CheckedMessageCacheError)
  | messageReference (error : ReferenceProjectionError)
  deriving Repr, DecidableEq

/-- The checked ordinary rule's value-independent execution shape. A once plan pins every repeatable error-field level to row 1 without claiming that row exists in document topology. -/
inductive OrdinaryRuleIterationPlan where
  | scalar
  | once (errorScope : List RepeatableLevel)
  | rows (scope : List RepeatableLevel)
  deriving Repr, DecidableEq

/-- Partial execution distinguishes a whole-rule filtered skip from the ordered validation-row scan; each environment then keeps the iteration-bound error-path gate separate from every evaluated verdict. -/
inductive PartialRepeatableRuleOutcome where
  | skipped
  | evaluated (rows : List (Env × PartialRuleOutcome))
  deriving Repr, DecidableEq

/-- Preserve the observable distinction between no rule evaluation and one evaluated pinned instance; UNKNOWN remains inside the evaluated outcome. -/
inductive PartialOnceRuleOutcome where
  | skipped
  | evaluated (environment : Env) (outcome : FlatRuleOutcome)
  deriving Repr, DecidableEq

/-- The error path may extend the condition's iteration scope: its remaining coordinates stay at one (RuleIterationLimitCreator; retained iteration-domain GroupSeen controls). A mixed rule with no per-row scope may retain a repeatable error path for once evaluation; scalar flat-rule assembly keeps its nonrepeatable invariant. -/
def ruleErrorScopeCompatible (allowRepeatableOnce : Bool)
    (declaration : FlatFieldDecl) :
    Option (List RepeatableLevel) → Bool
  | none => allowRepeatableOnce || declaration.repeatableScope.isEmpty
  | some scope => scope.isPrefixOf declaration.repeatableScope

/-- A complete resolved rule whose condition and explicit error field are certified against the same validated model. The condition projection and reference traversal are parameters so flat and mixed rules share one metadata certificate. -/
structure CheckedResolvedRule (allowRepeatableOnce : Bool)
    (model : FlatModel)
    (CheckedCondition CoreCondition : Type)
    (coreOf : CheckedCondition → CoreCondition)
    (referencesField : CoreCondition → FieldId → Bool)
    (iterationScopeOf : CoreCondition →
      Except ValidationCondition.RuleIterationScopeError
        (Option (List RepeatableLevel))) where
  condition : CheckedCondition
  errorField : FieldId
  errorCode : String
  severity : ValidationSeverity
  messagePlan : MessageRenderPlan
  errorDeclaration : FlatFieldDecl
  errorFieldLookup :
    model.lookupUniqueId errorField = .ok errorDeclaration
  iterationScope : Option (List RepeatableLevel)
  iterationScopeOwned :
    iterationScopeOf (coreOf condition) = .ok iterationScope
  errorFieldScopeCompatible :
    ruleErrorScopeCompatible allowRepeatableOnce
      errorDeclaration iterationScope = true
  errorFieldReferenced :
    referencesField (coreOf condition) errorField = true

abbrev CheckedResolvedFlatRule (model : FlatModel) :=
  CheckedResolvedRule false model (CheckedFlatCondition model) FlatCondition
    (fun condition => condition.core) FlatCondition.referencesField
    (fun _ =>
      (.ok none :
        Except ValidationCondition.RuleIterationScopeError
          (Option (List RepeatableLevel))))

abbrev ResolvedValidationRule (model : FlatModel) :=
  ResolvedRule (ValidationCondition model)

abbrev CheckedResolvedValidationRule (model : FlatModel) :=
  CheckedResolvedRule true model (CheckedValidationCondition model)
    (ValidationCondition model)
    (fun condition => condition.core)
    (fun condition field => condition.referencesErrorField field)
    ValidationCondition.ordinaryIterationScope

namespace CheckedResolvedFlatRule

def core (rule : CheckedResolvedFlatRule model) : ResolvedFlatRule :=
  { condition := rule.condition.core
    errorField := rule.errorField
    errorCode := rule.errorCode
    severity := rule.severity
    messagePlan := rule.messagePlan }

def evalFull (rule : CheckedResolvedFlatRule model)
    (prepared : PreparedFlatStringContext model compilePattern)
    (locale : String) (raw : RawFlatContext) (hasContent : Bool) :
    FlatRuleOutcome :=
  ResolvedRule.evalFull rule.core
    ((prepared.checkContext locale raw).withWorld prepared.world) hasContent

end CheckedResolvedFlatRule

namespace ResolvedValidationRule

def emitEvaluationResult (rule : ResolvedValidationRule model)
    (result : Except ScalarTemporalEvaluationFault Verdict) : FlatRuleOutcome :=
  match result with
  | .ok verdict => rule.emit verdict
  | .error _ => rule.emitRuntimeFailureAt []

def evalFull (rule : ResolvedValidationRule model)
    (context : ValidationEvaluationContext)
    (hasContent : Bool) : FlatRuleOutcome :=
  if hasContent || rule.condition.canFireOnEmpty then
    rule.emitEvaluationResult (rule.condition.evalSelectedResult context)
  else .notFired

/-- Emit at one resolved error path after effectful addressed condition evaluation. Structural addressing failure remains an outer error and therefore cannot manufacture UNKNOWN or a message. -/
def evalAddressedFullAt (rule : ResolvedValidationRule model)
    (context : AddressedValidationEvaluationContext model)
    (hasContent : Bool) (errorPath : List Nat) :
    Except CheckedAddressingError FlatRuleOutcome := do
  if !hasContent && !rule.condition.canFireOnEmpty then return .notFired
  match rule.condition.evalAddressedWithRepetitionNotUniqueResult context none with
  | .ok verdict => pure (rule.emitAt errorPath verdict)
  | .error (.inl error) => throw error
  | .error (.inr _) => pure (rule.emitRuntimeFailureAt errorPath)

/-- The established addressed entry is the nonrepeatable error-path specialization. -/
def evalAddressedFull (rule : ResolvedValidationRule model)
    (context : AddressedValidationEvaluationContext model)
    (hasContent : Bool) : Except CheckedAddressingError FlatRuleOutcome :=
  rule.evalAddressedFullAt context hasContent []

end ResolvedValidationRule

namespace CheckedResolvedValidationRule

/-- Expose the explicit ordinary execution decision already certified by condition scope plus the error declaration. -/
def ordinaryIterationPlan
    (rule : CheckedResolvedValidationRule model) :
    OrdinaryRuleIterationPlan :=
  match rule.iterationScope with
  | some scope => .rows scope
  | none =>
      if rule.errorDeclaration.repeatableScope.isEmpty then
        .scalar
      else
        .once rule.errorDeclaration.repeatableScope

/-- The partial rule-run gate compares only repetition levels actually selected by the checked iteration plan. Scalar and once plans bind none; a row plan binds its reference-derived scope. -/
def partialErrorBoundLevels
    (rule : CheckedResolvedValidationRule model) : List RepeatableLevel :=
  match rule.ordinaryIterationPlan with
  | .rows scope => scope
  | .scalar | .once _ => []

/-- Preserve the condition-bound coordinates and pin only the non-iterating error suffix to one.
The iteration-domain and peer iteration-group captures distinguish this from extending rule iteration. -/
def errorPathAt (rule : CheckedResolvedValidationRule model) (environment : Env) :
    Except OrdinaryRepeatableRuleEvaluationError (List Nat) := do
  let bound ← (environment.pathForScope (rule.iterationScope.getD [])).mapError
    (fun cause => .addressing (.environment cause))
  pure (bound ++ List.replicate (rule.errorDeclaration.repeatableScope.length - bound.length) 1)

/-- Whether the complete checked rule contains a `Having` filter anywhere in its condition. A partial-validation compiler or executor must query this before relevance, iteration, or branch evaluation. -/
def hasHaving
    (rule : CheckedResolvedValidationRule model) : Bool :=
  rule.condition.hasHaving

def requiresAddressedValidation
    (rule : CheckedResolvedValidationRule model) : Bool :=
  rule.condition.core.requiresAddressedValidation

def core (rule : CheckedResolvedValidationRule model) :
    ResolvedValidationRule model :=
  { condition := rule.condition.core
    errorField := rule.errorField
    errorCode := rule.errorCode
    severity := rule.severity
    messagePlan := rule.messagePlan }

def evalFull (rule : CheckedResolvedValidationRule model)
    (prepared : PreparedFlatStringContext model compilePattern)
    (locale : String) (raw : RawFlatContext) (groups : GroupPresenceContext)
    (hasContent : Bool) :
    Except ValidationEvaluationError FlatRuleOutcome :=
  if rule.requiresAddressedValidation then
    .error .addressedContextRequired
  else
    .ok (ResolvedValidationRule.evalFull rule.core
      { fields := (prepared.checkContext locale raw).withWorld prepared.world, groups }
      hasContent)

/-- Execute one checked nonrepeatable scalar rule under kernel 30.8.1 partial validation. The observational admission normal form makes every filtered rule skip, global fields augment the caller scope for the independent error-field gate, relevant rules bypass the full-validation content gate, and out-of-set leaf reads remain UNKNOWN inside the existing connective evaluator. An addressed condition uses `evalAddressedPartial` instead. Kernel dispatches by error field before entering the generated rule method; that unobservable internal order is not represented here. -/
def evalPartial (rule : CheckedResolvedValidationRule model)
    (prepared : PreparedFlatStringContext model compilePattern)
    (locale : String) (raw : RawFlatContext) (groups : GroupPresenceContext)
    (scope : ValidationRelevanceScope) :
    Except ValidationEvaluationError PartialRuleOutcome :=
  let effective := scope.withGlobals model
  let isRelevant : FlatRelevance := fun field =>
    effective.coversField model field []
  let errorRelevant := effective.coversFieldAtBoundLevels model
    rule.errorField rule.partialErrorBoundLevels []
  let filterPresence : FlatRuleFilterPresence :=
    if rule.hasHaving then .filtered else .unfiltered
  if !filterPresence.admits fun _ => errorRelevant then
    .ok .skipped
  else if rule.requiresAddressedValidation then
    .error .addressedContextRequired
  else
    let context : ValidationEvaluationContext := {
      fields := (prepared.checkContext locale raw).withWorld prepared.world
      groups
      pass := .part }
    .ok (.evaluated
      (rule.core.emitEvaluationResult (rule.condition.core.evalSelectedResult context isRelevant)))

/-- Build the callback's four channels from the current checked view. Formal findings are never
filtered by callback-hidden dependencies; partial generated failures augment the base findings,
and unbound error coordinates remain unknown (spec/11 §14). -/
def withCustomConditions (rule : CheckedResolvedValidationRule model)
    (context : AddressedValidationEvaluationContext model)
    (relevance : CustomConditionRelevance ValidationRelevanceScope)
    (registry : CustomValidationRegistry model)
    (generatedFormalFailures : List CellAddr := []) : AddressedValidationEvaluationContext model :=
  let invoke := match context.input with
    | .legacy _ _ => fun _ => .error .unavailableInvocation
    | .checked document | .partialView document _ =>
      let errorPointer : MessagePointer := {
        field := rule.errorField
        coordinates := rule.errorDeclaration.repeatableScope.map fun level =>
          (context.outer.uniqueRowAt? level).map MessageRepetitionCoordinate.concrete |>.getD .unknown }
      let invocation :=
        CustomValidationInvocation.ofDocument document relevance errorPointer generatedFormalFailures
      fun name => registry.evaluate name invocation
  { context with scalar := { context.scalar with customConditions := invoke } }

/-- Evaluate a model-certified addressed rule through the same checked core and message emitter. The caller must supply one coherent prepared scalar/repeatable view; SG1 remains responsible for constructing that view from a general document. -/
def evalAddressedFull (rule : CheckedResolvedValidationRule model)
    (context : AddressedValidationEvaluationContext model)
    (hasContent : Bool) (registry : CustomValidationRegistry model := {}) : Except CheckedAddressingError FlatRuleOutcome :=
  rule.core.evalAddressedFull (rule.withCustomConditions context .all registry) hasContent

private def toOrdinaryRowEnvironmentError :
    ActualRowEnvironmentError → OrdinaryRepeatableRuleEvaluationError
  | .missingScope => .missingIterationScope
  | .unknownLevel level => .incoherentIterationScope [level]
  | .incoherentScope supplied _ => .incoherentIterationScope supplied
  | .incoherentRow row => .incoherentRow row

private def ordinaryRepeatableFieldIds
    (rule : CheckedResolvedValidationRule model) : List FieldId :=
  (rule.condition.core.ordinaryRepeatableFields.map (·.id)).eraseDups

private def NatPath.isPrefixOf : List Nat → List Nat → Bool
  | [], _ => true
  | _, [] => false
  | expected :: expectedRest, actual :: actualRest =>
      expected == actual && NatPath.isPrefixOf expectedRest actualRest

/-- Full once evaluation uses admitted value-content in the error field's root instance. Explicit repeated descendants also dispatch their containing root (iteration-domain root-gate grid, 2026-10-04). -/
def ordinaryOnceRootHasContent
    (rule : CheckedResolvedValidationRule model)
    (checked : CheckedDocument model) (environment : Env) :
    Except CheckedAddressingError Bool := do
  let root := rule.errorDeclaration.groupPath.take 1
  let rootScope := model.repeatableScopeForGroupPath root
  let addressPrefix ←
    (environment.pathForScope rootScope).mapError .environment
  pure ((checked.validationDispatchedRoots root).contains (addressPrefix.headD 1))

/-- Construct the all-one environment of a checked once plan. Scalar and row-iteration plans remain explicit structural mismatches. -/
def onceEnvironment
    (rule : CheckedResolvedValidationRule model) :
    Except OrdinaryRepeatableRuleEvaluationError Env :=
  match rule.ordinaryIterationPlan with
  | .scalar => throw .missingIterationScope
  | .rows _ => throw .unsupportedCondition
  | .once scope => pure (scope.map fun level => (level, 1))

/-- Whether every leaf has an exact relevance-aware addressed interpretation. `false` is a structural execution error, not semantic UNKNOWN. -/
def supportsOrdinaryRepeatablePartial
    (rule : CheckedResolvedValidationRule model) : Bool :=
  rule.condition.core.allLeaves
    ValidationConditionLeaf.supportsAddressedPartial

/-- Partial operand walks can reach missing declared coordinates (KF527, spec/10 §5).
Read those slots without materializing rows, then apply the relevance-scoped generated findings.
`none` retains call-local silent unavailability rather than inventing a formal cause. -/
def partialValidationAddressedCell?
    (preliminary : CheckedPartialPreliminary model)
    (environment : Env) (field : FieldId) :
    Except CheckedAddressingError (Option CheckedCell) := do
  let addressed ←
    preliminary.index.base.addressedCellWithRead preliminary.index.base.readDeclared environment field
  if !preliminary.isAddressRelevant addressed.address ||
      preliminary.silentlyUnavailable.contains addressed.address then
    pure none
  else
    pure (some (preliminary.annotateAuthoredCell
      addressed.address addressed.cell))

private inductive OrdinaryRuleStep where
  | next (row : Env) (outcome : FlatRuleOutcome)
  | abort (row : Env) (outcome : FlatRuleOutcome)

private def OrdinaryRuleStep.outcome : OrdinaryRuleStep → FlatRuleOutcome
  | .next _ outcome | .abort _ outcome => outcome

/-- Error addressing uses the structural key even when another branch fires. Runtime failures
keep the iterator address because the generated catch bypasses reanchoring (spec/08 §4.3). -/
private def reanchorSelectedError (rule : CheckedResolvedValidationRule model)
    (environment : Env) (outcome : FlatRuleOutcome)
    (inputs : Unit → Except OrdinaryRepeatableRuleEvaluationError MessageReferenceInputs) :
    Except OrdinaryRepeatableRuleEvaluationError FlatRuleOutcome := do
  let .fired message := outcome | return outcome
  if message.origin == .runtimeFailure then return outcome
  let some selection := rule.condition.core.uniqueErrorSelection? rule.errorField
      (rule.iterationScope.getD []) | return outcome
  let inputs ← inputs ()
  let (_, coordinate, _) ← inputs.resolveIndex selection.group selection.indexDeclaration
    selection.key environment |>.mapError .messageReference
  let position := selection.indexDeclaration.repeatableScope.length - 1
  pure (.fired { message with errorAddress := { message.errorAddress with
    coordinates := message.errorAddress.coordinates.set position coordinate } })

private def fullMessageReferenceInputs (checked : CheckedDocument model) :
    Except OrdinaryRepeatableRuleEvaluationError MessageReferenceInputs := do
  let preliminary ← checked.applyFullIndexPreliminary |>.mapError .preliminary
  preliminary.messageReferenceInputs |>.mapError .messageCache

/-- The addressed context of one partial instance, before any custom-condition callbacks. -/
def _root_.A12Kernel.CheckedPartialPreliminary.addressedValidationContext
    (preliminary : CheckedPartialPreliminary model) (environment : Env)
    (world : Option World := none) : AddressedValidationEvaluationContext model := {
  scalar := {
    fields := { preliminary.index.base.flatContext with world }
    groups := GroupPresenceContext.unavailable
  }
  outer := environment
  input := .partialView preliminary.index.base (partialValidationAddressedCell? preliminary)
}

/-- The relevance-aware verdict of `condition` at `environment` in a partial call. Reached temporal
faults stay distinct from structural errors, for the caller's runtime-failure handler. -/
def _root_.A12Kernel.ValidationCondition.evalPartialAddressedResult (condition : ValidationCondition model)
    (preliminary : CheckedPartialPreliminary model)
    (context : AddressedValidationEvaluationContext model) (environment : Env)
    (repetitionNotUniqueResult? : Option RepetitionNotUniqueResult) :
    Except (Sum OrdinaryRepeatableRuleEvaluationError ScalarTemporalEvaluationFault) Verdict :=
  let checked := preliminary.index.base
  let scope := preliminary.relevance
  let isRelevant : FlatRelevance := fun field =>
    scope.coversField model field environment
  let resolveGroup (groupPath : GroupPath) (current : Env) :=
    (preliminary.groupPresenceInput groupPath current false).mapError .group
  condition.evalWithTemporalResult context.scalar isRelevant (fun leaf =>
      match leaf.evalAddressedPartial? context scope isRelevant resolveGroup repetitionNotUniqueResult? with
      | some result => result.mapError (fun error => .inl (.conditionAddressing error))
      | none => .error (.inl .unsupportedCondition)) (.error (.inl .unsupportedCondition))
      (onTemporalValueFailure := fun fault => .error (.inr fault))
      (leafRuntimeFault? := fun
        | .inl (.conditionAddressing error) => ValidationCondition.ruleRuntimeFailure? error
        | _ => none)
      (firstFilledResult := fun comparison =>
        match comparison.evaluatePartial? checked environment context.scalar.fields scope context.readPartialCell with
        | none => .error (.inl (.inl .unsupportedCondition))
        | some result => result.mapError fun
            | .inl error => .inl (.inl (.conditionAddressing error))
            | .inr fault => .inr fault)
      (temporalPartialResult? := fun leaf =>
        (leaf.evalTemporalPartialResult? context scope).map (Except.mapError fun
          | .inl error => .inl (.inl (.conditionAddressing error))
          | .inr fault => .inr fault))
      (numericResult := fun comparison =>
        match comparison.evalAddressedPartialResult? context scope isRelevant resolveGroup with
        | none => .error (.inl (.inl (.conditionAddressing .temporalUnavailable)))
        | some result => result.mapError fun
            | .inl error => .inl (.inl (.conditionAddressing error))
            | .inr fault => .inr fault)
      (customResult := fun name => (context.scalar.customResult name).mapError
        (fun error => .inl (.conditionAddressing (.customCondition error))))

/-- Evaluate an already-admitted partial instance at a derived target path. The caller owns filtering, relevance admission, and path construction; this helper owns leaf evaluation and message emission. -/
private def evalOrdinaryPartialAdmittedAt
    (rule : CheckedResolvedValidationRule model)
    (preliminary : CheckedPartialPreliminary model)
    (environment : Env)
    (errorPath : List Nat)
    (repetitionNotUniqueResult? : Option RepetitionNotUniqueResult)
    (failureErrorPath : List Nat := errorPath)
    (world : Option World := none)
    (registry : CustomValidationRegistry model := {}) :
    Except OrdinaryRepeatableRuleEvaluationError OrdinaryRuleStep := do
  let context := rule.withCustomConditions (preliminary.addressedValidationContext environment world)
    (.partialEntities preliminary.relevance) registry preliminary.generatedFormalFailures
  let result := rule.condition.core.evalPartialAddressedResult preliminary context environment
    repetitionNotUniqueResult?
  match result with
  | .ok verdict => do
      let outcome ← rule.reanchorSelectedError environment (rule.core.emitAt errorPath verdict)
        (fun _ => preliminary.messageReferenceInputs |>.mapError .messageCache)
      pure (.next environment outcome)
  | .error (.inl error) => throw error
  | .error (.inr (.addressing error)) =>
      if ValidationCondition.caughtByRule error then
        pure (.abort environment (rule.core.emitRuntimeFailureAt failureErrorPath))
      else throw (.conditionAddressing error)
  | .error (.inr _) => pure (.abort environment (rule.core.emitRuntimeFailureAt failureErrorPath))

/-- Execute one checked nonrepeatable addressed rule against the normalized partial document view. The scalar iteration plan fixes the empty environment and root error path; filtering and error-field relevance still gate execution before addressed leaf reads, while unsupported shapes and addressing failures remain structural errors outside semantic UNKNOWN. -/
def evalAddressedPartial
    (rule : CheckedResolvedValidationRule model)
    (checked : CheckedDocument model)
    (scope : ValidationRelevanceScope)
    (world : Option World := none)
    (registry : CustomValidationRegistry model := {}) :
    Except OrdinaryRepeatableRuleEvaluationError PartialRuleOutcome := do
  if rule.hasHaving then
    pure .skipped
  else
    match rule.ordinaryIterationPlan with
    | .once _ | .rows _ => throw .unsupportedCondition
    | .scalar =>
        if !rule.supportsOrdinaryRepeatablePartial then
          throw .unsupportedCondition
        let preliminary ←
          checked.applyPartialGeneratedPreliminaryForScope scope
            |>.mapError .preliminary
        if !preliminary.relevance.coversFieldAtBoundLevels model
            rule.errorField rule.partialErrorBoundLevels [] then
          pure .skipped
        else
          pure (.evaluated
            (← rule.evalOrdinaryPartialAdmittedAt preliminary [] [] none (world := world) (registry := registry)).outcome)

/-- Prepare each branch-independent RNU relation once per existing bound prefix. Partial scope excludes incomplete composite keys before reads; full scope retains every topology row. The checked source and rule must agree on the complete deepest-row iteration scope. -/
private def repetitionNotUniqueResults
    (rule : CheckedResolvedValidationRule model)
    (checked : CheckedDocument model)
    (scope : ValidationRelevanceScope) (environments : List Env)
    (fullDomain : Bool := false) :
    Except OrdinaryRepeatableRuleEvaluationError
      (List RepetitionNotUniqueResult) :=
  match rule.condition.core.repetitionNotUniqueSource? with
  | none => pure []
  | some source =>
      let sourceScope := source.topology.path.axes.map (·.level)
      if rule.iterationScope != some sourceScope then
        throw .unsupportedCondition
      else do
        let outerEnvironments ← environments.mapM fun environment =>
          (source.topology.path.boundEnvironment environment)
            |>.mapError fun error =>
              .conditionAddressing (.addressing error)
        let scopedResults ← outerEnvironments.eraseDups.mapM fun outer =>
          (source.evaluateChecked checked outer scope fullDomain)
            |>.mapError .conditionAddressing
        pure scopedResults.flatten

/-- Evaluate one validation-produced ordinary environment against an already-normalized partial preliminary view. An error path not relevant at the plan's bound levels skips before addressed reads; an admitted row maps only nonrelevant supported leaves to semantic UNKNOWN. -/
def evalOrdinaryRepeatablePartialAtPrepared
    (rule : CheckedResolvedValidationRule model)
    (preliminary : CheckedPartialPreliminary model)
    (environment : Env)
    (world : Option World := none)
    (registry : CustomValidationRegistry model := {}) :
    Except OrdinaryRepeatableRuleEvaluationError
      (Env × PartialRuleOutcome) := do
  if !rule.supportsOrdinaryRepeatablePartial then
    throw .unsupportedCondition
  let checked := preliminary.index.base
  if !preliminary.relevance.coversFieldAtBoundLevels model rule.errorField
      rule.partialErrorBoundLevels environment then
    pure (environment, .skipped)
  else
    let repetitionNotUniqueResults ←
      rule.repetitionNotUniqueResults checked preliminary.relevance [environment]
    let result? :=
      repetitionNotUniqueResults.find? fun result =>
        result.row == environment
    let errorPath ← rule.errorPathAt environment
    let outcome ←
      rule.evalOrdinaryPartialAdmittedAt preliminary
        environment errorPath result? (world := world) (registry := registry)
    pure (environment, .evaluated outcome.outcome)

/-- Convenience boundary for one row when the caller has not retained the call-local preliminary certificate. Filtered whole-rule execution still owns its earlier skip. -/
def evalOrdinaryRepeatablePartialAt
    (rule : CheckedResolvedValidationRule model)
    (checked : CheckedDocument model)
    (scope : ValidationRelevanceScope) (environment : Env)
    (world : Option World := none)
    (registry : CustomValidationRegistry model := {}) :
    Except OrdinaryRepeatableRuleEvaluationError
      (Env × PartialRuleOutcome) := do
  let preliminary ←
    checked.applyPartialGeneratedPreliminaryForScope scope
      |>.mapError .preliminary
  rule.evalOrdinaryRepeatablePartialAtPrepared preliminary environment world registry

private def evalOrdinaryRepeatableAt
    (rule : CheckedResolvedValidationRule model)
    (checked : CheckedDocument model) (environment : Env)
    (failureErrorPath : List Nat)
    (repetitionNotUniqueResult? : Option RepetitionNotUniqueResult := none)
    (world : Option World := none)
    (registry : CustomValidationRegistry model := {}) :
    Except OrdinaryRepeatableRuleEvaluationError OrdinaryRuleStep := do
  let _ ← rule.ordinaryRepeatableFieldIds.mapM fun field =>
    (checked.fullValidationAddressedCell environment field)
      |>.mapError .addressing
  let errorPath ← rule.errorPathAt environment
  let base := { checked.flatContext with world }
  let context : AddressedValidationEvaluationContext model := {
    scalar := { fields := base, groups := GroupPresenceContext.unavailable }
    outer := environment
    input := .checked checked
  }
  let context := rule.withCustomConditions context .all registry
  match rule.condition.core.evalAddressedWithRepetitionNotUniqueResult
      context repetitionNotUniqueResult? with
  | .ok verdict => do
      let outcome ← rule.reanchorSelectedError environment (rule.core.emitAt errorPath verdict)
        (fun _ => fullMessageReferenceInputs checked)
      pure (.next environment outcome)
  | .error (.inl error) => throw (.conditionAddressing error)
  | .error (.inr (.addressing error)) =>
      if ValidationCondition.caughtByRule error then
        pure (.abort environment (rule.core.emitRuntimeFailureAt failureErrorPath))
      else throw (.conditionAddressing error)
  | .error (.inr .calendarUnavailable) | .error (.inr .indexedOperandNotSupported) => throw (.conditionAddressing .temporalUnavailable)
  | .error (.inr .dateTimeLabelUnresolved) | .error (.inr .componentNumberInvalid) =>
      pure (.abort environment (rule.core.emitRuntimeFailureAt failureErrorPath))

/-- Full validation's row domain and the `RepetitionNotUnique` results its rows are evaluated
against. A fired message's references read the duplicate cluster from the same results. -/
def fullRowsAndRepetitionResults
    (rule : CheckedResolvedValidationRule model)
    (checked : CheckedDocument model) :
    Except OrdinaryRepeatableRuleEvaluationError (List Env × List RepetitionNotUniqueResult) := do
  let scope ← match rule.iterationScope with
    | some scope => pure scope
    | none => throw .missingIterationScope
  let environments ←
    checked.fullValidationRowEnvironments scope
      |>.mapError toOrdinaryRowEnvironmentError
  pure (environments, ← rule.repetitionNotUniqueResults checked .full environments true)

/-- Execute a checked ordinary nonparallel repeatable rule over the validation row domain. The root dispatcher and declared-capacity/occupied-prefix iterator own the domain (iteration grid, 2026-10-04). Repeated operands use the validation-only addressed view; the error address defaults its unbound suffix without reading or materializing that target. A runtime-aborted pair retains the failing environment, while its message points to the iterator’s first error address. -/
def evalOrdinaryRepeatableFull
    (rule : CheckedResolvedValidationRule model)
    (checked : CheckedDocument model) (world : Option World := none)
    (registry : CustomValidationRegistry model := {}) :
    Except OrdinaryRepeatableRuleEvaluationError
      (List (Env × FlatRuleOutcome)) := do
  if !rule.condition.core.supportsOrdinaryIteration then
    throw .unsupportedCondition
  let (environments, repetitionNotUniqueResults) ← rule.fullRowsAndRepetitionResults checked
  -- The generated rule handler surrounds the whole loop (CodeGenRuleDefinition.st), so a
  -- reached runtime failure keeps earlier messages and terminates before later row reads.
  -- Its error address uses EbenenIterator.get(), which restarts at the first environment.
  let failureErrorPath ← match environments with
    | [] => pure []
    | first :: _ =>
        rule.errorPathAt first
  let rec evaluate : List Env → Except OrdinaryRepeatableRuleEvaluationError
      (List (Env × FlatRuleOutcome))
    | [] => pure []
    | environment :: remaining => do
        let result? := (repetitionNotUniqueResults.find? (·.row == environment)).orElse fun _ =>
          rule.condition.core.repetitionNotUniqueSource?.map fun _ =>
            { row := environment, verdict := .notFired, cluster := [] }
        match ← rule.evalOrdinaryRepeatableAt checked environment failureErrorPath result? world registry with
        | .next row outcome => pure ((row, outcome) :: (← evaluate remaining))
        | .abort row outcome => pure [(row, outcome)]
  evaluate environments

/-- Execute the distinct no-per-row-reference rule shape exactly once. Every repeatable error level is pinned to row 1, but target addressing is derived from the checked declaration and never read or inserted as document topology. Full validation retains the root admitted-content gate before addressed condition reads unless the error field lies in a repeatable root group. -/
def evalOrdinaryOnceFull
    (rule : CheckedResolvedValidationRule model)
    (checked : CheckedDocument model) (world : Option World := none)
    (registry : CustomValidationRegistry model := {}) :
    Except OrdinaryRepeatableRuleEvaluationError
      (Env × FlatRuleOutcome) := do
  if !rule.condition.core.supportsOrdinaryIteration then
    throw .unsupportedCondition
  let environment ← rule.onceEnvironment
  -- A once rule whose error field lies in a repeatable root group runs with no content gate: the
  -- Kernel fires `Sum(/Rep*/P) < 5` declared on a `max 3` root once, at its first row, over a blank
  -- document ([checkpoint](../../docs/sources/group-list-and-capacity-probes.md#src-rule-bucket-empty-gate)).
  -- Under a nonrepeatable root the gate stays.
  let repeatableRoot := match rule.errorDeclaration.groupPath with
    | root :: _ => !(model.repeatableScopeForGroupPath [root]).isEmpty
    | [] => false
  let hasContent ←
    (rule.ordinaryOnceRootHasContent checked environment)
      |>.mapError .addressing
  let hasContent := hasContent || repeatableRoot
  let errorPath ← rule.errorPathAt environment
  let context : AddressedValidationEvaluationContext model := {
    scalar := {
      fields := { checked.flatContext with world }
      groups := GroupPresenceContext.unavailable
    }
    outer := environment
    input := .checked checked
  }
  let context := rule.withCustomConditions context .all registry
  let outcome ←
    (rule.core.evalAddressedFullAt context hasContent errorPath)
      |>.mapError .conditionAddressing
  let outcome ← rule.reanchorSelectedError environment outcome
    (fun _ => fullMessageReferenceInputs checked)
  pure (environment, outcome)

/-- Execute the once plan against an already-normalized partial preliminary view. A filtered rule skips before plan construction, an error path absent from the relevant set skips before condition reads, and an admitted path bypasses the full root-content gate. A once plan binds no repeatable level for this gate even though its message pointer defaults to the all-one environment. Relevance never creates the target row. -/
def evalOrdinaryOncePartialPrepared
    (rule : CheckedResolvedValidationRule model)
    (preliminary : CheckedPartialPreliminary model)
    (world : Option World := none)
    (registry : CustomValidationRegistry model := {}) :
    Except OrdinaryRepeatableRuleEvaluationError
      PartialOnceRuleOutcome := do
  if rule.hasHaving then
    pure .skipped
  else
    if !rule.supportsOrdinaryRepeatablePartial then
      throw .unsupportedCondition
    let environment ← rule.onceEnvironment
    if !preliminary.relevance.coversFieldAtBoundLevels model rule.errorField
        rule.partialErrorBoundLevels environment then
      pure .skipped
    else
      let errorPath ← rule.errorPathAt environment
      let outcome ←
        rule.evalOrdinaryPartialAdmittedAt preliminary
          environment errorPath none (world := world) (registry := registry)
      pure (.evaluated environment outcome.outcome)

/-- Convenience once boundary that prepares the normalized call-local view only after the rule-wide filter skip. -/
def evalOrdinaryOncePartial
    (rule : CheckedResolvedValidationRule model)
    (checked : CheckedDocument model)
    (scope : ValidationRelevanceScope)
    (world : Option World := none)
    (registry : CustomValidationRegistry model := {}) :
    Except OrdinaryRepeatableRuleEvaluationError
      PartialOnceRuleOutcome := do
  if rule.hasHaving then
    pure .skipped
  else
    let preliminary ←
      checked.applyPartialGeneratedPreliminaryForScope scope
        |>.mapError .preliminary
    rule.evalOrdinaryOncePartialPrepared preliminary world registry

/-- Execute a checked partial ordinary rule over one normalized call-local preliminary view and the validation row domain. Filtered rules skip before row construction. Error-path relevance is compared at the reference-derived levels bound by iteration, with deeper levels ignored, and never becomes document topology. -/
def evalOrdinaryRepeatablePartialPrepared
    (rule : CheckedResolvedValidationRule model)
    (preliminary : CheckedPartialPreliminary model)
    (world : Option World := none)
    (registry : CustomValidationRegistry model := {}) :
    Except OrdinaryRepeatableRuleEvaluationError
      PartialRepeatableRuleOutcome := do
  if rule.hasHaving then
    pure .skipped
  else
    if !rule.supportsOrdinaryRepeatablePartial then
      throw .unsupportedCondition
    let iterationScope ← match rule.iterationScope with
      | some iterationScope => pure iterationScope
      | none => throw .missingIterationScope
    let checked := preliminary.index.base
    let environments ←
      checked.validationRowEnvironments iterationScope
        |>.mapError toOrdinaryRowEnvironmentError
    let admittedEnvironments := environments.filter fun environment =>
      preliminary.relevance.coversFieldAtBoundLevels model rule.errorField
        rule.partialErrorBoundLevels environment
    let repetitionNotUniqueResults ←
      if admittedEnvironments.isEmpty then
        pure []
      else
        rule.repetitionNotUniqueResults checked preliminary.relevance
          admittedEnvironments
    let failureErrorPath ← match preliminary.relevance.iteratorStart? model rule.errorDeclaration.path
        rule.partialErrorBoundLevels environments with
      | none => pure []
      | some first => rule.errorPathAt first
    let rec evaluate : List Env → Except OrdinaryRepeatableRuleEvaluationError
        (List (Env × PartialRuleOutcome))
      | [] => pure []
      | environment :: remaining => do
          if !preliminary.relevance.coversFieldAtBoundLevels model rule.errorField
              rule.partialErrorBoundLevels environment then
            pure ((environment, .skipped) :: (← evaluate remaining))
          else
            let result? := repetitionNotUniqueResults.find? (·.row == environment)
            let errorPath ← rule.errorPathAt environment
            match ← rule.evalOrdinaryPartialAdmittedAt preliminary environment
                errorPath result? failureErrorPath world registry with
            | .next row outcome => pure ((row, .evaluated outcome) :: (← evaluate remaining))
            | .abort row outcome => pure [(row, .evaluated outcome)]
    pure (.evaluated (← evaluate environments))

/-- Convenience whole-rule boundary that prepares one normalized call-local view only after the rule-wide filter skip, then delegates every row to the prepared evaluator. -/
def evalOrdinaryRepeatablePartial
    (rule : CheckedResolvedValidationRule model)
    (checked : CheckedDocument model)
    (scope : ValidationRelevanceScope)
    (world : Option World := none)
    (registry : CustomValidationRegistry model := {}) :
    Except OrdinaryRepeatableRuleEvaluationError
      PartialRepeatableRuleOutcome := do
  if rule.hasHaving then
    pure .skipped
  else
    let preliminary ←
      checked.applyPartialGeneratedPreliminaryForScope scope
        |>.mapError .preliminary
    rule.evalOrdinaryRepeatablePartialPrepared preliminary world registry

end CheckedResolvedValidationRule

private def assembleResolvedRule (allowRepeatableOnce : Bool)
    (model : FlatModel)
    (coreOf : CheckedCondition → CoreCondition)
    (referencesField : CoreCondition → FieldId → Bool)
    (iterationScopeOf : CoreCondition →
      Except ValidationCondition.RuleIterationScopeError
        (Option (List RepeatableLevel)))
    (condition : CheckedCondition)
    (errorField : FieldId) (errorCode : String)
    (severity : ValidationSeverity)
    (messagePlan : MessageRenderPlan) :
    Except FlatRuleAssemblyError
      (CheckedResolvedRule allowRepeatableOnce model
        CheckedCondition CoreCondition
        coreOf referencesField iterationScopeOf) :=
  match hIteration : iterationScopeOf (coreOf condition) with
  | .error error => .error (.iterationScope error)
  | .ok iterationScope =>
    match hLookup : model.lookupUniqueId errorField with
    | .error error => .error (.errorField error)
    | .ok declaration =>
      if hScope :
          ruleErrorScopeCompatible allowRepeatableOnce
            declaration iterationScope = true then
        if hReferenced :
            referencesField (coreOf condition) errorField = true then
          .ok {
            condition
            errorField
            errorCode
            severity
            messagePlan
            errorDeclaration := declaration
            errorFieldLookup := hLookup
            iterationScope
            iterationScopeOwned := hIteration
            errorFieldScopeCompatible := hScope
            errorFieldReferenced := hReferenced
          }
        else
          .error (.errorFieldNotReferenced errorField)
      else
        match iterationScope with
        | none => .error (.repeatableErrorField errorField)
        | some expected =>
            .error (.iterationScopeMismatch errorField expected
              declaration.repeatableScope)

/-- Assemble the metadata boundary after condition elaboration. A repeatable error field is rejected before reference membership because this capsule has no row address. -/
def assembleResolvedFlatRule (model : FlatModel)
    (condition : CheckedFlatCondition model)
    (errorField : FieldId) (errorCode : String)
    (severity : ValidationSeverity)
    (messagePlan : MessageRenderPlan) :
  Except FlatRuleAssemblyError (CheckedResolvedFlatRule model) :=
  assembleResolvedRule false model (fun checked => checked.core)
    FlatCondition.referencesField
    (fun _ =>
      (.ok none :
        Except ValidationCondition.RuleIterationScopeError
          (Option (List RepeatableLevel))))
    condition errorField errorCode severity messagePlan

/-- Assemble the existing message/error-field boundary around a checked mixed condition. -/
def assembleResolvedValidationRule (model : FlatModel)
    (condition : CheckedValidationCondition model)
    (errorField : FieldId) (errorCode : String)
    (severity : ValidationSeverity)
    (messagePlan : MessageRenderPlan) :
  Except FlatRuleAssemblyError (CheckedResolvedValidationRule model) :=
  let assembled := (assembleResolvedRule true model (fun checked => checked.core)
    (fun core field => core.referencesErrorField field)
    ValidationCondition.ordinaryIterationScope
    condition errorField errorCode severity messagePlan).bind fun rule =>
      if condition.core.authoredErrorReference? errorField == some false then
        .error (.errorFieldNotReferenced errorField)
      else .ok rule
  -- The walk's refusal answers ahead of the per-level negative-condition gate, which is measured only
  -- where the error field binds the level; every other refusal keeps its place behind that gate
  -- ([inbound](../../docs/sources/inbound-handbacks.md#inbound-2026-09-24c-group-operand-walk)).
  match assembled with
  | .error error =>
      match error.unboundLevel? model condition.declaringGroup with
      | some (field, unbound) => .error (.unboundOperandLevel field unbound)
      | none =>
          match condition.core.iterationLegality with
          | .ok (.invalid level) => .error (.negativeConditionInIteration level)
          | .ok .legal | .ok (.insufficient _) | .error _ => .error error
  | .ok rule =>
      let errorGroup := rule.errorDeclaration.groupPath
      -- With the error field outside the rule group nothing binds a level, the rule group's own
      -- included, so an iterating rule whose error scope matches is refused all the same.
      match rule.iterationScope, WrittenFieldPlacement.of condition.declaringGroup errorGroup with
      | some (level :: _), .outside =>
          .error (.unboundOperandLevel errorField
            (model.unboundOperandLevel condition.declaringGroup errorGroup level))
      | _, _ =>
          let innerLevel? := (rule.iterationScope.getD []).find? fun level =>
            (model.repeatableGroupAtLevel? level).any (fun group => group.path.length > 1)
          if condition.core.formOnlyErrorReference? errorField == some true then
            match innerLevel? with
            | some level => .error (.formOnlyIteration errorField level)
            | none => finish rule
          else finish rule
where
  finish (rule : CheckedResolvedValidationRule model) :
      Except FlatRuleAssemblyError (CheckedResolvedValidationRule model) :=
          match (rule.iterationScope.getD []).find? (fun level =>
              condition.core.errorReferenceAt? errorField level == some false) with
          | some level => .error (.errorFieldIterationInvalid errorField level)
          | none =>
              match condition.core.iterationLegality with
              | .ok (.invalid level) => .error (.negativeConditionInIteration level)
              | .ok .legal | .ok (.insufficient _) | .error _ => .ok rule

end A12Kernel
