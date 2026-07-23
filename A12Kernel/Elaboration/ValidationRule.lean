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
  | errorFieldNotReferenced (field : FieldId)
  deriving Repr, DecidableEq

/-- A checked mixed rule cannot be evaluated from a scalar context when its condition retains an addressed source. This is missing execution context, not a semantic validation result. -/
inductive ValidationEvaluationError where
  | addressedContextRequired
  deriving Repr, DecidableEq

/-- A complete resolved rule whose condition and explicit error field are certified against the same validated model. The condition projection and reference traversal are parameters so flat and mixed rules share one metadata certificate. -/
structure CheckedResolvedRule (model : FlatModel)
    (CheckedCondition CoreCondition : Type)
    (coreOf : CheckedCondition → CoreCondition)
    (referencesField : CoreCondition → FieldId → Bool) where
  condition : CheckedCondition
  errorField : FieldId
  errorCode : String
  severity : ValidationSeverity
  messagePlan : MessageRenderPlan
  errorDeclaration : FlatFieldDecl
  errorFieldLookup :
    model.lookupUniqueId errorField = .ok errorDeclaration
  errorFieldNonrepeatable :
    errorDeclaration.repeatableScope.isEmpty = true
  errorFieldReferenced :
    referencesField (coreOf condition) errorField = true

abbrev CheckedResolvedFlatRule (model : FlatModel) :=
  CheckedResolvedRule model (CheckedFlatCondition model) FlatCondition
    (fun condition => condition.core) FlatCondition.referencesField

abbrev ResolvedValidationRule (model : FlatModel) :=
  ResolvedRule (ValidationCondition model)

abbrev CheckedResolvedValidationRule (model : FlatModel) :=
  CheckedResolvedRule model (CheckedValidationCondition model)
    (ValidationCondition model)
    (fun condition => condition.core)
    (fun condition field => condition.referencesField field)

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
    (condition : CheckedCondition)
    (errorField : FieldId) (errorCode : String)
    (severity : ValidationSeverity)
    (messagePlan : MessageRenderPlan) :
    Except FlatRuleAssemblyError
      (CheckedResolvedRule model CheckedCondition CoreCondition
        coreOf referencesField) :=
  match hLookup : model.lookupUniqueId errorField with
  | .error error => .error (.errorField error)
  | .ok declaration =>
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
            errorFieldNonrepeatable := hNonrepeatable
            errorFieldReferenced := hReferenced
          }
        else
          .error (.errorFieldNotReferenced errorField)
      else
        .error (.repeatableErrorField errorField)

/-- Assemble the metadata boundary after condition elaboration. A repeatable error field is rejected before reference membership because this capsule has no row address. -/
def assembleResolvedFlatRule (model : FlatModel)
    (condition : CheckedFlatCondition model)
    (errorField : FieldId) (errorCode : String)
    (severity : ValidationSeverity)
    (messagePlan : MessageRenderPlan) :
    Except FlatRuleAssemblyError (CheckedResolvedFlatRule model) :=
  assembleResolvedRule model (fun checked => checked.core)
    FlatCondition.referencesField condition errorField errorCode severity messagePlan

/-- Assemble the existing message/error-field boundary around a checked mixed condition. -/
def assembleResolvedValidationRule (model : FlatModel)
    (condition : CheckedValidationCondition model)
    (errorField : FieldId) (errorCode : String)
    (severity : ValidationSeverity)
    (messagePlan : MessageRenderPlan) :
    Except FlatRuleAssemblyError (CheckedResolvedValidationRule model) :=
  assembleResolvedRule model (fun checked => checked.core)
    (fun core field => core.referencesField field)
    condition errorField errorCode severity messagePlan

end A12Kernel
