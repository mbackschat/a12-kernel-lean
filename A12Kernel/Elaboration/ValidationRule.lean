import A12Kernel.Elaboration.StringContext
import A12Kernel.Elaboration.ValidationCondition
import A12Kernel.Elaboration.CheckedStarDocument
import A12Kernel.Semantics.ValidationRule

/-! # Checked assembly for resolved validation rules

This boundary consumes an existing checked flat or mixed condition and a resolved error-field ID. Surface rule syntax and authored message templates remain outside it.
-/

namespace A12Kernel

inductive FlatRuleAssemblyError where
  | errorField (error : ResolveError)
  | repeatableErrorField (field : FieldId)
  | iterationScope (error : ValidationCondition.RuleIterationScopeError)
  | iterationScopeMismatch (field : FieldId)
      (expected actual : List RepeatableLevel)
  | errorFieldNotReferenced (field : FieldId)
  | negativeConditionInIteration (level : RepeatableLevel)
  deriving Repr, DecidableEq

/-- A checked mixed rule cannot be evaluated from a scalar context when its condition retains an addressed source. This is missing execution context, not a semantic validation result. -/
inductive ValidationEvaluationError where
  | addressedContextRequired
  deriving Repr, DecidableEq

/-- Structural failures from the first checked ordinary repeatable rule route remain outside semantic UNKNOWN. -/
inductive OrdinaryRepeatableRuleEvaluationError where
  | missingIterationScope
  | unsupportedCondition
  | incoherentRow (row : RowAddr)
  | addressing (error : CheckedAddressingError)
  | conditionAddressing (error : CheckedAddressingError)
  deriving Repr, DecidableEq

/-- The checked ordinary rule's value-independent execution shape. A once plan pins every repeatable error-field level to row 1 without claiming that row exists in document topology. -/
inductive OrdinaryRuleIterationPlan where
  | scalar
  | once (errorScope : List RepeatableLevel)
  | rows (scope : List RepeatableLevel)
  deriving Repr, DecidableEq

/-- Partial execution distinguishes a whole-rule filtered skip from the ordered actual-row scan; each actual row then keeps error-instance skip separate from every evaluated verdict. -/
inductive PartialRepeatableRuleOutcome where
  | skipped
  | evaluated (rows : List (Env × PartialRuleOutcome))
  deriving Repr, DecidableEq

/-- Preserve the observable distinction between no rule evaluation and one evaluated pinned instance; UNKNOWN remains inside the evaluated outcome. -/
inductive PartialOnceRuleOutcome where
  | skipped
  | evaluated (environment : Env) (outcome : FlatRuleOutcome)
  deriving Repr, DecidableEq

/-- Row iteration requires the error field at the exact derived scope. A mixed rule with no per-row scope may instead retain a repeatable error path for once evaluation; scalar flat-rule assembly passes `false` and keeps its nonrepeatable invariant. -/
def ruleErrorScopeCompatible (allowRepeatableOnce : Bool)
    (declaration : FlatFieldDecl) :
    Option (List RepeatableLevel) → Bool
  | none => allowRepeatableOnce || declaration.repeatableScope.isEmpty
  | some scope => declaration.repeatableScope == scope

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
    (fun condition field => condition.referencesField field)
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

def evalFull (rule : ResolvedValidationRule model)
    (context : ValidationEvaluationContext)
    (hasContent : Bool) : FlatRuleOutcome :=
  rule.evalWith fun condition => condition.evalFull context hasContent

/-- Emit at one resolved error path after effectful addressed condition evaluation. Structural addressing failure remains an outer error and therefore cannot manufacture UNKNOWN or a message. -/
def evalAddressedFullAt (rule : ResolvedValidationRule model)
    (context : AddressedValidationEvaluationContext model)
    (hasContent : Bool) (errorPath : List Nat) :
    Except CheckedAddressingError FlatRuleOutcome := do
  pure (rule.emitAt errorPath
    (← rule.condition.evalAddressedFull context hasContent))

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

/-- Execute one checked nonrepeatable rule under kernel 30.8.1 partial validation. The observational admission normal form makes every filtered rule skip, global fields augment the caller scope for the independent error-field gate, relevant rules bypass the full-validation content gate, and out-of-set leaf reads remain UNKNOWN inside the existing connective evaluator. Kernel dispatches by error field before entering the generated rule method; that unobservable internal order is not represented here. -/
def evalPartial (rule : CheckedResolvedValidationRule model)
    (prepared : PreparedFlatStringContext model compilePattern)
    (locale : String) (raw : RawFlatContext) (groups : GroupPresenceContext)
    (scope : ValidationRelevanceScope) :
    Except ValidationEvaluationError PartialRuleOutcome :=
  let effective := scope.withGlobals model
  let isRelevant : FlatRelevance := fun field =>
    effective.coversField model field []
  let filterPresence : FlatRuleFilterPresence :=
    if rule.hasHaving then .filtered else .unfiltered
  if !filterPresence.admits fun _ => isRelevant rule.errorField then
    .ok .skipped
  else if rule.requiresAddressedValidation then
    .error .addressedContextRequired
  else
    let context : ValidationEvaluationContext := {
      fields := (prepared.checkContext locale raw).withWorld prepared.world
      groups }
    .ok (.evaluated
      (rule.core.emit (rule.condition.core.evalSelected context isRelevant)))

/-- Evaluate a model-certified addressed rule through the same checked core and message emitter. The caller must supply one coherent prepared scalar/repeatable view; SG1 remains responsible for constructing that view from a general document. -/
def evalAddressedFull (rule : CheckedResolvedValidationRule model)
    (context : AddressedValidationEvaluationContext model)
    (hasContent : Bool) : Except CheckedAddressingError FlatRuleOutcome :=
  rule.core.evalAddressedFull context hasContent

private def ordinaryIterationEnvironments
    (scope : List RepeatableLevel) (rows : List RowAddr) :
    Except OrdinaryRepeatableRuleEvaluationError (List Env) :=
  match scope.reverse with
  | [] => .error .missingIterationScope
  | deepest :: _ =>
      (rows.filter fun row => row.group == deepest).mapM fun row =>
        if row.path.length == scope.length then
          pure (scope.zip row.path)
        else
          throw (.incoherentRow row)

private def ordinaryRepeatableFieldIds
    (rule : CheckedResolvedValidationRule model) : List FieldId :=
  (rule.condition.core.ordinaryRepeatableFields.map (·.id)).eraseDups

private def NatPath.isPrefixOf : List Nat → List Nat → Bool
  | [], _ => true
  | _, [] => false
  | expected :: expectedRest, actual :: actualRest =>
      expected == actual && NatPath.isPrefixOf expectedRest actualRest

/-- Full once evaluation uses admitted value-content in the error field's root instance. Physical row existence is deliberately not part of this gate. -/
private def ordinaryOnceRootHasContent
    (rule : CheckedResolvedValidationRule model)
    (checked : CheckedDocument model) (environment : Env) :
    Except CheckedAddressingError Bool := do
  let root := rule.errorDeclaration.groupPath.take 1
  let rootScope := model.repeatableScopeForGroupPath root
  let addressPrefix ←
    (environment.pathForScope rootScope).mapError .environment
  pure (checked.checkedCells.any fun placement =>
    match model.lookupUniqueId placement.address.field with
    | .ok declaration =>
        root.isPrefixOf declaration.groupPath &&
          addressPrefix.isPrefixOf placement.address.path &&
          placement.cell.admitsGroupContent
    | .error _ => false)

/-- Construct the all-one environment of a checked once plan. Scalar and actual-row plans remain explicit structural mismatches. -/
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

/-- Evaluate an already-admitted partial instance at a derived target path. The caller owns filtering, relevance admission, and path construction; this helper owns leaf evaluation and message emission. -/
private def evalOrdinaryPartialAdmittedAt
    (rule : CheckedResolvedValidationRule model)
    (checked : CheckedDocument model)
    (scope : ValidationRelevanceScope) (environment : Env)
    (errorPath : List Nat) :
    Except OrdinaryRepeatableRuleEvaluationError FlatRuleOutcome := do
  let context : AddressedValidationEvaluationContext model := {
    scalar := {
      fields := checked.flatContext
      groups := GroupPresenceContext.unavailable
    }
    outer := environment
    input := .checked checked
  }
  let isRelevant : FlatRelevance := fun field =>
    scope.coversField model field environment
  let verdict ← rule.condition.core.evalVerdictExcept fun leaf =>
    match leaf.evalAddressedPartial? context scope isRelevant with
    | some result => result.mapError .conditionAddressing
    | none => throw .unsupportedCondition
  pure (rule.core.emitAt errorPath verdict)

/-- Evaluate one actual ordinary row under partial relevance. A nonrelevant error instance skips before addressed reads; an admitted row maps only nonrelevant supported leaves to semantic UNKNOWN. -/
def evalOrdinaryRepeatablePartialAt
    (rule : CheckedResolvedValidationRule model)
    (checked : CheckedDocument model)
    (scope : ValidationRelevanceScope) (environment : Env) :
    Except OrdinaryRepeatableRuleEvaluationError
      (Env × PartialRuleOutcome) := do
  if !rule.supportsOrdinaryRepeatablePartial then
    throw .unsupportedCondition
  let effective := scope.withGlobals model
  if !effective.coversField model rule.errorField environment then
    pure (environment, .skipped)
  else
    let errorCell ←
      (checked.addressedCell environment rule.errorField).mapError .addressing
    let outcome ←
      rule.evalOrdinaryPartialAdmittedAt checked effective
        environment errorCell.address.path
    pure (environment, .evaluated outcome)

private def evalOrdinaryRepeatableAt
    (rule : CheckedResolvedValidationRule model)
    (checked : CheckedDocument model) (environment : Env)
    (repetitionNotUniqueResult? : Option RepetitionNotUniqueResult := none) :
    Except OrdinaryRepeatableRuleEvaluationError (Env × FlatRuleOutcome) := do
  let _ ← rule.ordinaryRepeatableFieldIds.mapM fun field =>
    (checked.addressedCell environment field).mapError .addressing
  let errorCell ←
    (checked.addressedCell environment rule.errorField).mapError .addressing
  let base := checked.flatContext
  let context : AddressedValidationEvaluationContext model := {
    scalar := { fields := base, groups := GroupPresenceContext.unavailable }
    outer := environment
    input := .checked checked
  }
  let verdict ←
    (rule.condition.core.evalAddressedFullWithRepetitionNotUnique
      context true repetitionNotUniqueResult?)
      |>.mapError .conditionAddressing
  let outcome := rule.core.emitAt errorCell.address.path verdict
  pure (environment, outcome)

/-- Execute the first checked ordinary nonparallel repeatable rule family over actual deepest-scope rows in immutable document order. Every repeated read and the error target resolve through `CheckedDocument.addressedCell`; no declared tail or phantom row becomes an environment. -/
def evalOrdinaryRepeatableFull
    (rule : CheckedResolvedValidationRule model)
    (checked : CheckedDocument model) :
    Except OrdinaryRepeatableRuleEvaluationError
      (List (Env × FlatRuleOutcome)) := do
  if !rule.condition.core.supportsOrdinaryIteration then
    throw .unsupportedCondition
  let scope ← match rule.iterationScope with
    | some scope => pure scope
    | none => throw .missingIterationScope
  let environments ←
    ordinaryIterationEnvironments scope checked.source.instantiatedRows
  let repetitionNotUniqueResults ←
    match rule.condition.core.repetitionNotUniqueSource? with
    | none => pure []
    | some source =>
        let sourceScope := source.topology.path.axes.map (·.level)
        if !source.supportsOneLevelOrdinaryRule || sourceScope != scope then
          throw .unsupportedCondition
        (source.evaluateChecked checked [] .full)
          |>.mapError .conditionAddressing
  environments.mapM fun environment =>
    let result? :=
      repetitionNotUniqueResults.find? fun result =>
        result.row == environment
    rule.evalOrdinaryRepeatableAt checked environment result?

/-- Execute the distinct no-per-row-reference rule shape exactly once. Every repeatable error level is pinned to row 1, but target addressing is derived from the checked declaration and never read or inserted as document topology. Full validation retains the root admitted-content gate before addressed condition reads. -/
def evalOrdinaryOnceFull
    (rule : CheckedResolvedValidationRule model)
    (checked : CheckedDocument model) :
    Except OrdinaryRepeatableRuleEvaluationError
      (Env × FlatRuleOutcome) := do
  if !rule.condition.core.supportsOrdinaryIteration then
    throw .unsupportedCondition
  let environment ← rule.onceEnvironment
  let hasContent ←
    (rule.ordinaryOnceRootHasContent checked environment)
      |>.mapError .addressing
  let errorPath ←
    (environment.pathForScope rule.errorDeclaration.repeatableScope)
      |>.mapError (fun cause =>
        .addressing (.environment cause))
  let context : AddressedValidationEvaluationContext model := {
    scalar := {
      fields := checked.flatContext
      groups := GroupPresenceContext.unavailable
    }
    outer := environment
    input := .checked checked
  }
  let verdict ←
    (rule.condition.core.evalAddressedFull context hasContent)
      |>.mapError .conditionAddressing
  pure (environment, rule.core.emitAt errorPath verdict)

/-- Execute the once plan under partial validation. A filtered rule skips before plan construction, an irrelevant pinned error instance skips before condition reads, and an admitted instance bypasses the full root-content gate. Relevance never creates the target row. -/
def evalOrdinaryOncePartial
    (rule : CheckedResolvedValidationRule model)
    (checked : CheckedDocument model)
    (scope : ValidationRelevanceScope) :
    Except OrdinaryRepeatableRuleEvaluationError
      PartialOnceRuleOutcome := do
  if rule.hasHaving then
    pure .skipped
  else
    if !rule.supportsOrdinaryRepeatablePartial then
      throw .unsupportedCondition
    let environment ← rule.onceEnvironment
    let effective := scope.withGlobals model
    if !effective.coversField model rule.errorField environment then
      pure .skipped
    else
      let errorPath ←
        (environment.pathForScope rule.errorDeclaration.repeatableScope)
          |>.mapError (fun cause =>
            .addressing (.environment cause))
      let outcome ←
        rule.evalOrdinaryPartialAdmittedAt checked effective
          environment errorPath
      pure (.evaluated environment outcome)

/-- Execute a checked one-level partial ordinary rule over actual deepest-scope rows in immutable document order. Filtered rules skip before row construction. Caller relevance and model-owned globals gate each actual error instance; relevance never becomes document topology, so this route creates no phantom environment. -/
def evalOrdinaryRepeatablePartial
    (rule : CheckedResolvedValidationRule model)
    (checked : CheckedDocument model)
    (scope : ValidationRelevanceScope) :
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
    if iterationScope.length != 1 then
      throw .unsupportedCondition
    let environments ←
      ordinaryIterationEnvironments iterationScope
        checked.source.instantiatedRows
    let rows ← environments.mapM fun environment =>
      rule.evalOrdinaryRepeatablePartialAt checked scope environment
    pure (.evaluated rows)

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
  match condition.core.iterationLegality with
  | .ok (.invalid level) =>
      .error (.negativeConditionInIteration level)
  | .ok .legal | .ok (.insufficient _) | .error _ =>
      assembleResolvedRule true model (fun checked => checked.core)
        (fun core field => core.referencesField field)
        ValidationCondition.ordinaryIterationScope
        condition errorField errorCode severity messagePlan

end A12Kernel
