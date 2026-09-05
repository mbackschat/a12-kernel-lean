import A12Kernel.Proofs.ValidationCondition

/-! # Explicit-validity leaf laws

The wiring a leaf arm adds is exactly the part that can rot silently: a tree can start routing the
leaf through a different evaluator, or reporting a different field dependency, without any
conformance case noticing. These laws pin both to the family's own owners.
-/

namespace A12Kernel

/-- The tree delegates to the family's own evaluator behind the ordinary relevance gate, and adds nothing of its own. -/
@[simp]
theorem validationCondition_customFieldValidity_evalSelected
    (model : FlatModel) (leaf : CheckedCustomFieldValidityLeaf model)
    (context : ValidationEvaluationContext) (isRelevant : FlatRelevance) :
    (ValidationCondition.customFieldValidity leaf).evalSelected context isRelevant =
      (if isRelevant leaf.operand.source then
        leaf.evalAt context.fields .validation
      else
        .unknown) := by
  rfl

/-- A nonrelevant operand is UNKNOWN rather than a verdict, so partial coverage cannot make the predicate answer about a cell it never read. -/
theorem validationCondition_customFieldValidity_notRelevant
    (model : FlatModel) (leaf : CheckedCustomFieldValidityLeaf model)
    (context : ValidationEvaluationContext) (isRelevant : FlatRelevance)
    (notRelevant : isRelevant leaf.operand.source = false) :
    (ValidationCondition.customFieldValidity leaf).evalSelected context isRelevant =
      .unknown := by
  simp [validationCondition_customFieldValidity_evalSelected, notRelevant]

/-- Analyze sees exactly the operand as the leaf's field dependency. The authored type name is not a field and contributes none. -/
@[simp]
theorem validationCondition_customFieldValidity_referencesField
    (model : FlatModel) (leaf : CheckedCustomFieldValidityLeaf model)
    (field : FieldId) :
    (ValidationCondition.customFieldValidity leaf).referencesField field =
      (leaf.operand.source == field) := by
  rfl

end A12Kernel
