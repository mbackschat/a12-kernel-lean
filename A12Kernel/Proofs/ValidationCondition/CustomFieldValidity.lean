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

/-! ## The addressed partial route

The partial route reads through a call-local view with a third answer beside filled and unreadable:
**not covered**. These laws fix what the arm does with each, because the flag below admits the whole
family to that route and nothing else re-checks the arm behind it. -/

/-- The family is admitted to partial validation, which is what lets a rule carrying it run there at all. -/
@[simp]
theorem validationConditionLeaf_customFieldValidity_partialSupported
    (model : FlatModel) (leaf : CheckedCustomFieldValidityLeaf model) :
    (ValidationConditionLeaf.customFieldValidity leaf).supportsAddressedPartial =
      true := by
  rfl

/-- An uncovered cell is UNKNOWN and never reaches the validator. Absence gives the same answer, so no conformance row can separate this from the covered-but-empty case; the law is what states it. -/
theorem validationConditionLeaf_customFieldValidity_partialUncovered
    (model : FlatModel) (leaf : CheckedCustomFieldValidityLeaf model)
    (context : AddressedValidationEvaluationContext model)
    (scope : ValidationRelevanceScope) (isRelevant : FlatRelevance)
    (resolveGroup :
      GroupPath → Env →
        Except CheckedAddressingError ResolvedGroupPresenceInput)
    (repetitionNotUniqueResult? : Option RepetitionNotUniqueResult)
    (relevant : isRelevant leaf.operand.source = true)
    (uncovered :
      context.readPartialCell context.outer leaf.operand.source = .ok none) :
    ValidationConditionLeaf.evalAddressedPartial? context scope isRelevant
        resolveGroup repetitionNotUniqueResult?
        (.customFieldValidity leaf) = some (.ok .unknown) := by
  simp [ValidationConditionLeaf.evalAddressedPartial?, relevant, uncovered]
  rfl

/-- On a covered cell the partial route returns the family's own evaluator applied to that cell, so wherever the two reads agree the partial verdict is the scalar one. The arm cannot answer differently by construction; this states that it does not. -/
theorem validationConditionLeaf_customFieldValidity_partialCoveredAgrees
    (model : FlatModel) (leaf : CheckedCustomFieldValidityLeaf model)
    (context : AddressedValidationEvaluationContext model)
    (scope : ValidationRelevanceScope) (isRelevant : FlatRelevance)
    (resolveGroup :
      GroupPath → Env →
        Except CheckedAddressingError ResolvedGroupPresenceInput)
    (repetitionNotUniqueResult? : Option RepetitionNotUniqueResult)
    (cell : CheckedCell)
    (relevant : isRelevant leaf.operand.source = true)
    (covered :
      context.readPartialCell context.outer leaf.operand.source =
        .ok (some cell))
    (agrees : context.scalar.fields.read leaf.operand.source = cell) :
    ValidationConditionLeaf.evalAddressedPartial? context scope isRelevant
        resolveGroup repetitionNotUniqueResult?
        (.customFieldValidity leaf) =
      some (.ok ((ValidationCondition.customFieldValidity leaf).evalSelected
        context.scalar isRelevant)) := by
  simp [ValidationConditionLeaf.evalAddressedPartial?, relevant, covered,
    CheckedCustomFieldValidityLeaf.evalAt, agrees]
  rfl

end A12Kernel
