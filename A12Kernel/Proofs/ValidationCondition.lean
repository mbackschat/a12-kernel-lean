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

@[simp]
theorem conditionTree_allLeaves_map (condition : ConditionTree Source)
    (transform : Source → Target) (predicate : Target → Bool) :
    (condition.map transform).allLeaves predicate =
      condition.allLeaves (fun leaf => predicate (transform leaf)) := by
  induction condition with
  | leaf leaf => rfl
  | and left right leftIH rightIH | or left right leftIH rightIH =>
      simp only [ConditionTree.map, ConditionTree.allLeaves, leftIH, rightIH]

/-- Reusing the shared connective representation does not change any established flat verdict. -/
@[simp]
theorem validationCondition_flat_evalSelected
    (condition : FlatCondition) (context : ValidationEvaluationContext)
    (isRelevant : FlatRelevance) :
    (ValidationCondition.flat condition).evalSelected context isRelevant =
      condition.evalSelected context.fields isRelevant := by
  simp [ValidationCondition.flat, ValidationCondition.evalSelected,
    FlatCondition.evalSelected, ValidationConditionLeaf.evalSelected]

/-- The mixed tree's reference traversal preserves every reference in an embedded flat condition. -/
@[simp]
theorem validationCondition_flat_referencesField
    (condition : FlatCondition) (model : FlatModel) (field : FieldId) :
    (ValidationCondition.flat condition).referencesField model field =
      condition.referencesField field := by
  simp [ValidationCondition.flat, ValidationCondition.referencesField,
    FlatCondition.referencesField, ValidationConditionLeaf.referencesField]

/-- A relevant checked numeric comparison evaluates exactly as its existing resolved core. -/
@[simp]
theorem validationCondition_numeric_evalSelected_of_relevant
    (comparison : NumericComparison) (context : ValidationEvaluationContext)
    (isRelevant : FlatRelevance)
    (relevant : comparison.allRelevant isRelevant = true) :
    (ValidationCondition.numeric comparison).evalSelected context isRelevant =
      comparison.evalSelected context.fields := by
  simp [ValidationCondition.numeric, ValidationCondition.evalSelected,
    ValidationConditionLeaf.evalSelected, relevant]

/-- A reached resolved group leaf delegates exactly to the established product-state operator. -/
@[simp]
theorem validationCondition_groupPresence_evalSelected
    (operator : GroupPresenceOperator) (reference : ResolvedGroupReference)
    (context : ValidationEvaluationContext) (state : GroupPresenceState)
    (resolved : context.groups reference.path = some state)
    (isRelevant : FlatRelevance) :
    (ValidationCondition.groupPresence operator reference).evalSelected
        context isRelevant = operator.eval state := by
  simp [ValidationCondition.groupPresence, ValidationCondition.evalSelected,
    ValidationConditionLeaf.evalSelected, resolved]

/-- Missing checked-document group state is explicit semantic unavailability. -/
@[simp]
theorem validationCondition_groupPresence_missing_isUnknown
    (operator : GroupPresenceOperator) (reference : ResolvedGroupReference)
    (context : ValidationEvaluationContext)
    (missing : context.groups reference.path = none)
    (isRelevant : FlatRelevance) :
    (ValidationCondition.groupPresence operator reference).evalSelected
        context isRelevant = .unknown := by
  simp [ValidationCondition.groupPresence, ValidationCondition.evalSelected,
    ValidationConditionLeaf.evalSelected, missing]

/-- A reached fixed field/group list delegates once to the shared entity-presence tally and preserves its conservative collapsed-result embedding. -/
@[simp]
theorem validationCondition_groupList_evalSelected
    (operator : GroupFillQuantifier)
    (operands : List ResolvedGroupListOperand)
    (context : ValidationEvaluationContext)
    (isRelevant : FlatRelevance) :
    (ValidationCondition.groupList operator operands).evalSelected
        context isRelevant =
      (operator.evalPresence
        (operands.map fun operand =>
          operand.evalPresence context isRelevant)).asConservativeVerdict := by
  rfl

/-- The conservative embedding loses only the unobservable false/unknown distinction; it preserves every fired result and its exact polarity. -/
theorem validationCondition_groupList_fired_iff
    (operator : GroupFillQuantifier)
    (operands : List ResolvedGroupListOperand)
    (context : ValidationEvaluationContext)
    (isRelevant : FlatRelevance)
    (polarity : Polarity) :
    (ValidationCondition.groupList operator operands).evalSelected
        context isRelevant = .fired polarity ↔
      operator.evalPresence
        (operands.map fun operand =>
          operand.evalPresence context isRelevant) = .fired polarity := by
  rw [validationCondition_groupList_evalSelected]
  generalize operator.evalPresence
      (List.map (fun operand =>
        operand.evalPresence context isRelevant) operands) = outcome
  cases outcome <;> simp [ValidationFillOutcome.asConservativeVerdict]

/-- The checked mixed wrapper carries one model and exact row-group certificate for its complete resolved core. -/
theorem checkedValidationCondition_coherent
    (condition : CheckedValidationCondition model) :
    model.validate.isOk = true ∧
      condition.core.wellFormedBool model condition.rowGroup = true :=
  ⟨condition.modelWellFormed, condition.wellFormed⟩

end A12Kernel
