import A12Kernel.Elaboration.Flat
import A12Kernel.Semantics.ValidationRule

/-! # Checked assembly for one flat validation rule

This boundary consumes an existing checked flat condition and a resolved error-field ID. Surface rule syntax and authored message templates remain outside it.
-/

namespace A12Kernel

namespace FlatCondition

/-- Whether this already-resolved condition references one field ID. Error-field legality is checked after path resolution, never by authored path spelling. -/
def referencesField : FlatCondition → FieldId → Bool
  | .compare comparison, field => comparison.fieldId == field
  | .fieldFilled referenced, field
  | .fieldNotFilled referenced, field => referenced.id == field
  | .and left right, field
  | .or left right, field =>
      left.referencesField field || right.referencesField field

end FlatCondition

inductive FlatRuleAssemblyError where
  | errorField (error : ResolveError)
  | repeatableErrorField (field : FieldId)
  | errorFieldNotReferenced (field : FieldId)
  deriving Repr, DecidableEq

/-- A complete resolved flat rule whose condition and explicit error field are certified against the same validated model. -/
structure CheckedResolvedFlatRule (model : FlatModel) where
  condition : CheckedFlatCondition model
  errorField : FieldId
  errorCode : String
  severity : ValidationSeverity
  resolvedText : ResolvedMessageText
  errorDeclaration : FlatFieldDecl
  errorFieldLookup :
    model.lookupUniqueId errorField = .ok errorDeclaration
  errorFieldNonrepeatable :
    errorDeclaration.repeatableScope.isEmpty = true
  errorFieldReferenced :
    condition.core.referencesField errorField = true

namespace CheckedResolvedFlatRule

def core (rule : CheckedResolvedFlatRule model) : ResolvedFlatRule :=
  { condition := rule.condition.core
    errorField := rule.errorField
    errorCode := rule.errorCode
    severity := rule.severity
    resolvedText := rule.resolvedText }

def evalFull (rule : CheckedResolvedFlatRule model) (raw : RawFlatContext)
    (hasContent : Bool) : FlatRuleOutcome :=
  rule.core.evalFull (model.checkContext raw) hasContent

end CheckedResolvedFlatRule

/-- Assemble the metadata boundary after condition elaboration. A repeatable error field is rejected before reference membership because this capsule has no row address. -/
def assembleResolvedFlatRule (model : FlatModel)
    (condition : CheckedFlatCondition model)
    (errorField : FieldId) (errorCode : String)
    (severity : ValidationSeverity)
    (resolvedText : ResolvedMessageText) :
    Except FlatRuleAssemblyError (CheckedResolvedFlatRule model) :=
  match hLookup : model.lookupUniqueId errorField with
  | .error error => .error (.errorField error)
  | .ok declaration =>
      if hNonrepeatable : declaration.repeatableScope.isEmpty = true then
        if hReferenced : condition.core.referencesField errorField = true then
          .ok {
            condition
            errorField
            errorCode
            severity
            resolvedText
            errorDeclaration := declaration
            errorFieldLookup := hLookup
            errorFieldNonrepeatable := hNonrepeatable
            errorFieldReferenced := hReferenced
          }
        else
          .error (.errorFieldNotReferenced errorField)
      else
        .error (.repeatableErrorField errorField)

end A12Kernel
