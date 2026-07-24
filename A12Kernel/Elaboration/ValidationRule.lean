import A12Kernel.Elaboration.StringContext
import A12Kernel.Elaboration.ValidationCondition
import A12Kernel.Semantics.ValidationRule

/-! # Checked assembly for resolved validation rules

This boundary consumes an existing checked flat or mixed condition and a resolved error-field ID. Surface rule syntax and authored message templates remain outside it.
-/

namespace A12Kernel

inductive FlatRuleAssemblyError where
  | errorField (error : ResolveError)
  | repeatableErrorField (field : FieldId)
  | iterationSource (error : RuleIterationSourceError)
  | iterationScopeMismatch (field : FieldId)
      (expected actual : List RepeatableLevel)
  | errorFieldNotReferenced (field : FieldId)
  deriving Repr, DecidableEq

/-- A checked mixed rule cannot be evaluated from a scalar context when its condition retains an addressed source. This is missing execution context, not a semantic validation result. -/
inductive ValidationEvaluationError where
  | addressedContextRequired
  deriving Repr, DecidableEq

/-- Whether one error declaration can be addressed by the optional iteration source derived from the checked condition. -/
def ruleErrorScopeCompatible (declaration : FlatFieldDecl) :
    Option (CheckedStarFieldPath model) → Bool
  | none => declaration.repeatableScope.isEmpty
  | some source =>
      declaration.repeatableScope == source.path.axes.map (·.level)

/-- A complete resolved rule whose condition and explicit error field are certified against the same validated model. The condition projection and reference traversal are parameters so flat and mixed rules share one metadata certificate. -/
structure CheckedResolvedRule (model : FlatModel)
    (CheckedCondition CoreCondition : Type)
    (coreOf : CheckedCondition → CoreCondition)
    (referencesField : CoreCondition → FieldId → Bool)
    (iterationSourceOf : CoreCondition →
      Except RuleIterationSourceError
        (Option (CheckedStarFieldPath model))) where
  condition : CheckedCondition
  errorField : FieldId
  errorCode : String
  severity : ValidationSeverity
  messagePlan : MessageRenderPlan
  errorDeclaration : FlatFieldDecl
  errorFieldLookup :
    model.lookupUniqueId errorField = .ok errorDeclaration
  iterationSource : Option (CheckedStarFieldPath model)
  iterationSourceOwned :
    iterationSourceOf (coreOf condition) = .ok iterationSource
  errorFieldScopeCompatible :
    ruleErrorScopeCompatible errorDeclaration iterationSource = true
  errorFieldReferenced :
    referencesField (coreOf condition) errorField = true

abbrev CheckedResolvedFlatRule (model : FlatModel) :=
  CheckedResolvedRule model (CheckedFlatCondition model) FlatCondition
    (fun condition => condition.core) FlatCondition.referencesField
    (fun _ => .ok none)

abbrev ResolvedValidationRule (model : FlatModel) :=
  ResolvedRule (ValidationCondition model)

abbrev CheckedResolvedValidationRule (model : FlatModel) :=
  CheckedResolvedRule model (CheckedValidationCondition model)
    (ValidationCondition model)
    (fun condition => condition.core)
    (fun condition field => condition.referencesField field)
    ValidationCondition.iterationSource

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

/-- Emit through the sole rule-message boundary after effectful addressed condition evaluation. Structural addressing failure remains an outer error and therefore cannot manufacture UNKNOWN or a message. -/
def evalAddressedFull (rule : ResolvedValidationRule model)
    (context : AddressedValidationEvaluationContext model)
    (hasContent : Bool) : Except StarAddressingError FlatRuleOutcome := do
  pure (rule.emit (← rule.condition.evalAddressedFull context hasContent))

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
    (hasContent : Bool) : Except StarAddressingError FlatRuleOutcome :=
  rule.core.evalAddressedFull context hasContent

end CheckedResolvedValidationRule

private def assembleResolvedRule (model : FlatModel)
    (coreOf : CheckedCondition → CoreCondition)
    (referencesField : CoreCondition → FieldId → Bool)
    (iterationSourceOf : CoreCondition →
      Except RuleIterationSourceError
        (Option (CheckedStarFieldPath model)))
    (condition : CheckedCondition)
    (errorField : FieldId) (errorCode : String)
    (severity : ValidationSeverity)
    (messagePlan : MessageRenderPlan) :
    Except FlatRuleAssemblyError
      (CheckedResolvedRule model CheckedCondition CoreCondition
        coreOf referencesField iterationSourceOf) :=
  match hIteration : iterationSourceOf (coreOf condition) with
  | .error error => .error (.iterationSource error)
  | .ok iterationSource =>
    match hLookup : model.lookupUniqueId errorField with
    | .error error => .error (.errorField error)
    | .ok declaration =>
      match iterationSource with
      | none =>
        if hNonrepeatable : declaration.repeatableScope.isEmpty = true then
          if hReferenced : referencesField (coreOf condition) errorField = true then
            .ok {
              condition
              errorField
              errorCode
              severity
              messagePlan
              errorDeclaration := declaration
              errorFieldLookup := hLookup
              iterationSource := none
              iterationSourceOwned := hIteration
              errorFieldScopeCompatible := by
                simp [ruleErrorScopeCompatible, hNonrepeatable]
              errorFieldReferenced := hReferenced
            }
          else
            .error (.errorFieldNotReferenced errorField)
        else
          .error (.repeatableErrorField errorField)
      | some source =>
        let expected := source.path.axes.map (·.level)
        if hScope : declaration.repeatableScope = expected then
          if hReferenced : referencesField (coreOf condition) errorField = true then
            .ok {
              condition
              errorField
              errorCode
              severity
              messagePlan
              errorDeclaration := declaration
              errorFieldLookup := hLookup
              iterationSource := some source
              iterationSourceOwned := hIteration
              errorFieldScopeCompatible := by
                simp only [ruleErrorScopeCompatible, beq_iff_eq]
                exact hScope
              errorFieldReferenced := hReferenced
            }
          else
            .error (.errorFieldNotReferenced errorField)
        else
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
    FlatCondition.referencesField (fun _ => .ok none)
    condition errorField errorCode severity messagePlan

/-- Assemble the existing message/error-field boundary around a checked mixed condition. -/
def assembleResolvedValidationRule (model : FlatModel)
    (condition : CheckedValidationCondition model)
    (errorField : FieldId) (errorCode : String)
    (severity : ValidationSeverity)
    (messagePlan : MessageRenderPlan) :
    Except FlatRuleAssemblyError (CheckedResolvedValidationRule model) :=
  assembleResolvedRule model (fun checked => checked.core)
    (fun core field => core.referencesField field)
    ValidationCondition.iterationSource
    condition errorField errorCode severity messagePlan

end A12Kernel
