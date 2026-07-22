import A12Kernel.Elaboration.ValidationCondition

/-! # Shared validation-condition laws

These laws show that the shared connective tree preserves an established flat condition exactly and that embedding a checked numeric comparison adds only its relevance gate.
-/

namespace A12Kernel

@[simp]
theorem conditionTree_evalVerdict_map (condition : ConditionTree Source)
    (transform : Source → Target) (evalLeaf : Target → Verdict) :
    (condition.map transform).evalVerdict evalLeaf =
      condition.evalVerdict (fun leaf => evalLeaf (transform leaf)) := by
  induction condition with
  | leaf leaf => rfl
  | and left right leftIH rightIH =>
      simp only [ConditionTree.map, ConditionTree.evalVerdict, leftIH, rightIH]
  | or left right leftIH rightIH =>
      simp only [ConditionTree.map, ConditionTree.evalVerdict, leftIH, rightIH]

@[simp]
theorem conditionTree_anyLeaf_map (condition : ConditionTree Source)
    (transform : Source → Target) (predicate : Target → Bool) :
    (condition.map transform).anyLeaf predicate =
      condition.anyLeaf (fun leaf => predicate (transform leaf)) := by
  induction condition with
  | leaf leaf => rfl
  | and left right leftIH rightIH | or left right leftIH rightIH =>
      simp only [ConditionTree.map, ConditionTree.anyLeaf, leftIH, rightIH]

/-- Reusing the shared connective representation does not change any established flat verdict. -/
@[simp]
theorem validationCondition_flat_evalSelected
    (condition : FlatCondition) (context : FlatContext)
    (isRelevant : FlatRelevance) :
    (ValidationCondition.flat condition).evalSelected context isRelevant =
      condition.evalSelected context isRelevant := by
  simp [ValidationCondition.flat, ValidationCondition.evalSelected,
    FlatCondition.evalSelected, ValidationConditionLeaf.evalSelected]

/-- The mixed tree's reference traversal preserves every reference in an embedded flat condition. -/
@[simp]
theorem validationCondition_flat_referencesField
    (condition : FlatCondition) (field : FieldId) :
    (ValidationCondition.flat condition).referencesField field =
      condition.referencesField field := by
  simp [ValidationCondition.flat, ValidationCondition.referencesField,
    FlatCondition.referencesField, ValidationConditionLeaf.referencesField]

/-- A relevant checked numeric comparison evaluates exactly as its existing resolved core. -/
@[simp]
theorem validationCondition_numeric_evalSelected_of_relevant
    (comparison : NumericComparison) (context : FlatContext)
    (isRelevant : FlatRelevance)
    (relevant : comparison.allRelevant isRelevant = true) :
    (ValidationCondition.numeric comparison).evalSelected context isRelevant =
      comparison.evalSelected context := by
  simp [ValidationCondition.numeric, ValidationCondition.evalSelected,
    ValidationConditionLeaf.evalSelected, relevant]

end A12Kernel
