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

/-- The first ordinary repeatable rule route requires the error field to inhabit the exact deepest compatible nonparallel reference scope. Wider indirect group-reference anchoring remains outside this capsule. -/
def ruleErrorScopeCompatible (declaration : FlatFieldDecl) :
    Option (List RepeatableLevel) → Bool
  | none => declaration.repeatableScope.isEmpty
  | some scope => declaration.repeatableScope == scope

/-- A complete resolved rule whose condition and explicit error field are certified against the same validated model. The condition projection and reference traversal are parameters so flat and mixed rules share one metadata certificate. -/
structure CheckedResolvedRule (model : FlatModel)
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
    ruleErrorScopeCompatible errorDeclaration iterationScope = true
  errorFieldReferenced :
    referencesField (coreOf condition) errorField = true

abbrev CheckedResolvedFlatRule (model : FlatModel) :=
  CheckedResolvedRule model (CheckedFlatCondition model) FlatCondition
    (fun condition => condition.core) FlatCondition.referencesField
    (fun _ =>
      (.ok none :
        Except ValidationCondition.RuleIterationScopeError
          (Option (List RepeatableLevel))))

abbrev ResolvedValidationRule (model : FlatModel) :=
  ResolvedRule (ValidationCondition model)

abbrev CheckedResolvedValidationRule (model : FlatModel) :=
  CheckedResolvedRule model (CheckedValidationCondition model)
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

end CheckedResolvedValidationRule

private def assembleResolvedRule (model : FlatModel)
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
      (CheckedResolvedRule model CheckedCondition CoreCondition
        coreOf referencesField iterationScopeOf) :=
  match hIteration : iterationScopeOf (coreOf condition) with
  | .error error => .error (.iterationScope error)
  | .ok iterationScope =>
    match hLookup : model.lookupUniqueId errorField with
    | .error error => .error (.errorField error)
    | .ok declaration =>
      if hScope :
          ruleErrorScopeCompatible declaration iterationScope = true then
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
  assembleResolvedRule model (fun checked => checked.core)
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
      assembleResolvedRule model (fun checked => checked.core)
        (fun core field => core.referencesField field)
        ValidationCondition.ordinaryIterationScope
        condition errorField errorCode severity messagePlan

end A12Kernel
