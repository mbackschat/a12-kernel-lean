import A12Kernel.Elaboration.NumericValidation

/-! # Shared resolved validation conditions

This boundary joins the established flat leaves and resolved numeric-expression comparisons under one connective tree. It deliberately begins after each leaf family's checked elaboration; a later checked whole-rule capsule must preserve those certificates rather than accepting forged cores.
-/

namespace A12Kernel

/-- The two currently resolved validation leaf families. -/
inductive ValidationConditionLeaf where
  | flat (condition : FlatConditionLeaf)
  | numeric (comparison : NumericComparison)
  deriving Repr, DecidableEq

/-- One connective tree whose leaves may be ordinary flat clauses or resolved numeric-expression comparisons. -/
abbrev ValidationCondition := ConditionTree ValidationConditionLeaf

namespace ValidationCondition

/-- Embed an established flat tree without retaining a nested connective tree. -/
def flat (condition : FlatCondition) : ValidationCondition :=
  condition.map .flat

/-- Admit one resolved numeric comparison as a leaf. Checked construction remains with `CheckedNumericComparison`. -/
def numeric (comparison : NumericComparison) : ValidationCondition :=
  .leaf (.numeric comparison)

end ValidationCondition

namespace ValidationConditionLeaf

def canFireOnEmpty : ValidationConditionLeaf → Bool
  | .flat condition => condition.canFireOnEmpty
  | .numeric _ => false

def referencesField : ValidationConditionLeaf → FieldId → Bool
  | .flat condition, field => condition.referencesField field
  | .numeric comparison, field => comparison.referencesField field

/-- Evaluate one reached leaf with its own relevance rule. Numeric expressions require every field atom, while flat leaf rules retain their existing operator-specific checks. -/
def evalSelected (context : FlatContext) (isRelevant : FlatRelevance) :
    ValidationConditionLeaf → Verdict
  | .flat condition => condition.evalSelected context isRelevant
  | .numeric comparison =>
      if comparison.allRelevant isRelevant then comparison.evalSelected context
      else .unknown

end ValidationConditionLeaf

namespace ValidationCondition

def canFireOnEmpty (condition : ValidationCondition) : Bool :=
  condition.evalBool ValidationConditionLeaf.canFireOnEmpty

def referencesField (condition : ValidationCondition) (field : FieldId) : Bool :=
  condition.anyLeaf fun leaf => leaf.referencesField field

/-- Evaluate a row-selected mixed tree through the sole connective evaluator. -/
def evalSelected (condition : ValidationCondition) (context : FlatContext)
    (isRelevant : FlatRelevance := fun _ => true) : Verdict :=
  condition.evalVerdict fun leaf => leaf.evalSelected context isRelevant

/-- Apply the ordinary full-validation content gate to a mixed resolved tree. -/
def evalFull (condition : ValidationCondition) (context : FlatContext)
    (hasContent : Bool) : Verdict :=
  if hasContent || condition.canFireOnEmpty then condition.evalSelected context
  else .notFired

end ValidationCondition

end A12Kernel
