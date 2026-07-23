import A12Kernel.Elaboration.NumericValidation
import A12Kernel.Elaboration.SingleGroup
import A12Kernel.Semantics.GroupPresence

/-! # Shared resolved validation conditions

This boundary joins the established flat leaves and resolved numeric-expression comparisons under one connective tree. It deliberately begins after each leaf family's checked elaboration; a later checked whole-rule capsule must preserve those certificates rather than accepting forged cores.
-/

namespace A12Kernel

/-- The currently resolved validation leaf families. -/
inductive ValidationConditionLeaf where
  | flat (condition : FlatConditionLeaf)
  | numeric (scope : NumericOperandScope) (comparison : NumericComparison)
  | groupPresence (operator : GroupPresenceOperator)
      (reference : ResolvedGroupReference)
  deriving Repr, DecidableEq

/-- One connective tree whose leaves may be ordinary flat clauses or resolved numeric-expression comparisons. -/
abbrev ValidationCondition := ConditionTree ValidationConditionLeaf

namespace ValidationCondition

/-- Embed an established flat tree without retaining a nested connective tree. -/
def flat (condition : FlatCondition) : ValidationCondition :=
  condition.map .flat

/-- Admit one resolved numeric comparison as a leaf. Checked construction remains with `CheckedNumericComparison`. -/
def numeric (comparison : NumericComparison) : ValidationCondition :=
  .leaf (.numeric .sameGroup comparison)

/-- Preserve the checked operand policy when embedding a numeric comparison. -/
def numericIn (scope : NumericOperandScope)
    (comparison : NumericComparison) : ValidationCondition :=
  .leaf (.numeric scope comparison)

/-- Embed one resolved scalar group-presence predicate without re-traversing document state. -/
def groupPresence (operator : GroupPresenceOperator)
    (reference : ResolvedGroupReference) : ValidationCondition :=
  .leaf (.groupPresence operator reference)

end ValidationCondition

/-- Runtime group states are supplied by the checked-document boundary and keyed by resolved group path. Missing state is explicit unavailability. -/
abbrev GroupPresenceContext := GroupPath → Option GroupPresenceState

namespace GroupPresenceContext

/-- Explicitly provide no resolved group slices to a condition known to use only other leaf families. -/
def unavailable : GroupPresenceContext := fun _ => none

end GroupPresenceContext

/-- The shared checked-condition evaluator keeps field observations and already-resolved group states separate. -/
structure ValidationEvaluationContext where
  fields : FlatContext
  groups : GroupPresenceContext

namespace ResolvedGroupReference

/-- A scalar group-presence leaf either names a nonrepeatable ordinary group, or uses `RuleGroup` to bind the already-selected concrete rule instance. Wider repeatable addressing must be resolved before this boundary grows. -/
def scalarPresenceWellFormedBool (reference : ResolvedGroupReference)
    (model : FlatModel) (rowGroup : GroupPath) : Bool :=
  model.hasGroupPath reference.path &&
    match reference.origin with
    | .path => (model.repeatableScopeForGroupPath reference.path).isEmpty
    | .ruleGroup => reference.path == rowGroup

end ResolvedGroupReference

namespace ValidationConditionLeaf

def canFireOnEmpty : ValidationConditionLeaf → Bool
  | .flat condition => condition.canFireOnEmpty
  | .numeric _ _ => false
  | .groupPresence operator _ => operator.canFireOnEmpty

def referencesField (model : FlatModel) : ValidationConditionLeaf → FieldId → Bool
  | .flat condition, field => condition.referencesField field
  | .numeric _ comparison, field => comparison.referencesField field
  | .groupPresence _ reference, field => reference.referencesField model field

/-- Static admission reuses each leaf family's existing checked core predicate. -/
def wellFormedBool (model : FlatModel) (rowGroup : GroupPath) :
    ValidationConditionLeaf → Bool
  | .flat condition => condition.wellFormedBool model
  | .numeric scope comparison =>
      comparison.wellFormedInBool model rowGroup scope
  | .groupPresence _ reference =>
      reference.scalarPresenceWellFormedBool model rowGroup

/-- Evaluate one reached leaf with its own relevance rule. Numeric expressions require every field atom, while flat leaf rules retain their existing operator-specific checks. -/
def evalSelected (context : ValidationEvaluationContext)
    (isRelevant : FlatRelevance) :
    ValidationConditionLeaf → Verdict
  | .flat condition => condition.evalSelected context.fields isRelevant
  | .numeric _ comparison =>
      if comparison.allRelevant isRelevant then comparison.evalSelected context.fields
      else .unknown
  | .groupPresence operator reference =>
      match context.groups reference.path with
      | some state => operator.eval state
      | none => .unknown

end ValidationConditionLeaf

namespace ValidationCondition

def canFireOnEmpty (condition : ValidationCondition) : Bool :=
  condition.evalBool ValidationConditionLeaf.canFireOnEmpty

def referencesField (condition : ValidationCondition) (model : FlatModel)
    (field : FieldId) : Bool :=
  condition.anyLeaf fun leaf => leaf.referencesField model field

def wellFormedBool (condition : ValidationCondition)
    (model : FlatModel) (rowGroup : GroupPath) : Bool :=
  condition.allLeaves fun leaf => leaf.wellFormedBool model rowGroup

/-- Evaluate a row-selected mixed tree through the sole connective evaluator. -/
def evalSelected (condition : ValidationCondition)
    (context : ValidationEvaluationContext)
    (isRelevant : FlatRelevance := fun _ => true) : Verdict :=
  condition.evalVerdict fun leaf => leaf.evalSelected context isRelevant

/-- Apply the ordinary full-validation content gate to a mixed resolved tree. -/
def evalFull (condition : ValidationCondition)
    (context : ValidationEvaluationContext)
    (hasContent : Bool) : Verdict :=
  if hasContent || condition.canFireOnEmpty then condition.evalSelected context
  else .notFired

end ValidationCondition

inductive ValidationConditionAssemblyError where
  | invalidModel (error : ResolveError)
  | groupReference (error : SingleGroupElabError)
  | unknownGroup (path : GroupPath)
  | repeatableGroupRequiresAddress (path : GroupPath)
  | rowGroupMismatch (left right : GroupPath)
  | incoherentCore
  deriving Repr, DecidableEq

/-- A mixed resolved tree certified against one validated model and one exact rule-instance group. -/
structure CheckedValidationCondition (model : FlatModel) where
  rowGroup : GroupPath
  core : ValidationCondition
  modelWellFormed : model.validate.isOk = true
  wellFormed : core.wellFormedBool model rowGroup = true

namespace CheckedValidationCondition

/-- Certify a resolved mixed core once after a semantic desugaring has assembled its complete tree. -/
def checkCore (model : FlatModel) (rowGroup : GroupPath)
    (core : ValidationCondition) (modelWellFormed : model.validate.isOk = true) :
    Except ValidationConditionAssemblyError (CheckedValidationCondition model) :=
  if hCore : core.wellFormedBool model rowGroup = true then
    .ok { rowGroup, core, modelWellFormed, wellFormed := hCore }
  else
    .error .incoherentCore

/-- Lift a checked flat tree without nesting or changing its connective shape. -/
def fromFlat (condition : CheckedFlatCondition model) :
    Except ValidationConditionAssemblyError (CheckedValidationCondition model) :=
  checkCore model condition.rowGroup (ValidationCondition.flat condition.core)
    condition.modelWellFormed

/-- Lift one checked numeric comparison at its certified rule-instance group. -/
def fromNumeric (comparison : CheckedNumericComparison model) :
    Except ValidationConditionAssemblyError (CheckedValidationCondition model) :=
  checkCore model comparison.rowGroup
    (ValidationCondition.numericIn comparison.operandScope comparison.core)
    comparison.modelWellFormed

/-- Resolve and certify one scalar group-presence predicate against the same model and declaring group used by the surrounding rule. -/
def fromGroupPresence (model : FlatModel) (rowGroup : GroupPath)
    (reference : SurfaceGroupReference) (operator : GroupPresenceOperator) :
    Except ValidationConditionAssemblyError (CheckedValidationCondition model) :=
  match hModel : model.validate with
  | .error error => .error (.invalidModel error)
  | .ok () =>
      match reference.resolveAgainst rowGroup with
      | .error error => .error (.groupReference error)
      | .ok resolved =>
          if model.hasGroupPath resolved.path then
            match resolved.origin with
            | .path =>
                if (model.repeatableScopeForGroupPath resolved.path).isEmpty then
                  checkCore model rowGroup
                    (ValidationCondition.groupPresence operator resolved)
                    (by rw [hModel]; rfl)
                else
                  .error (.repeatableGroupRequiresAddress resolved.path)
            | .ruleGroup =>
                checkCore model rowGroup
                  (ValidationCondition.groupPresence operator resolved)
                  (by rw [hModel]; rfl)
          else
            .error (.unknownGroup resolved.path)

private def combine (constructor : ValidationCondition → ValidationCondition →
    ValidationCondition) (left right : CheckedValidationCondition model) :
    Except ValidationConditionAssemblyError (CheckedValidationCondition model) :=
  if left.rowGroup == right.rowGroup then
    checkCore model left.rowGroup (constructor left.core right.core)
      left.modelWellFormed
  else
    .error (.rowGroupMismatch left.rowGroup right.rowGroup)

def and (left right : CheckedValidationCondition model) :
    Except ValidationConditionAssemblyError (CheckedValidationCondition model) :=
  combine .and left right

def or (left right : CheckedValidationCondition model) :
    Except ValidationConditionAssemblyError (CheckedValidationCondition model) :=
  combine .or left right

end CheckedValidationCondition

end A12Kernel
