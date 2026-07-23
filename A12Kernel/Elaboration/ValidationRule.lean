import A12Kernel.Elaboration.Flat
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

abbrev ResolvedValidationRule := ResolvedRule ValidationCondition

abbrev CheckedResolvedValidationRule (model : FlatModel) :=
  CheckedResolvedRule model (CheckedValidationCondition model) ValidationCondition
    (fun condition => condition.core)
    (fun condition field => condition.referencesField model field)

namespace CheckedResolvedFlatRule

def core (rule : CheckedResolvedFlatRule model) : ResolvedFlatRule :=
  { condition := rule.condition.core
    errorField := rule.errorField
    errorCode := rule.errorCode
    severity := rule.severity
    messagePlan := rule.messagePlan }

def evalFull (rule : CheckedResolvedFlatRule model) (world : World) (raw : RawFlatContext)
    (hasContent : Bool) : FlatRuleOutcome :=
  ResolvedRule.evalFull rule.core
    ((model.checkContext raw).withWorld world) hasContent

end CheckedResolvedFlatRule

namespace ResolvedValidationRule

def evalFull (rule : ResolvedValidationRule)
    (context : ValidationEvaluationContext)
    (hasContent : Bool) : FlatRuleOutcome :=
  rule.evalWith fun condition => condition.evalFull context hasContent

end ResolvedValidationRule

namespace CheckedResolvedValidationRule

def core (rule : CheckedResolvedValidationRule model) : ResolvedValidationRule :=
  { condition := rule.condition.core
    errorField := rule.errorField
    errorCode := rule.errorCode
    severity := rule.severity
    messagePlan := rule.messagePlan }

def evalFull (rule : CheckedResolvedValidationRule model) (world : World)
    (raw : RawFlatContext) (groups : GroupPresenceContext)
    (hasContent : Bool) : FlatRuleOutcome :=
  ResolvedValidationRule.evalFull rule.core
    { fields := (model.checkContext raw).withWorld world, groups } hasContent

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
    (fun core field => core.referencesField model field)
    condition errorField errorCode severity messagePlan

end A12Kernel
