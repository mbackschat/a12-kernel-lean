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

/-- A decisive left non-fire keeps an unreachable structural failure on the right outside the addressed result. -/
theorem conditionTree_evalVerdictExcept_and_notFired_hidesRight
    (left right : ConditionTree Source)
    (evalLeaf : Source → Except Error Verdict)
    (leftResult : left.evalVerdictExcept evalLeaf = .ok .notFired) :
    (ConditionTree.and left right).evalVerdictExcept evalLeaf =
      Except.ok .notFired := by
  rw [ConditionTree.evalVerdictExcept, leftResult]
  rfl

/-- A decisive left VALUE firing likewise keeps an unreachable structural failure on the right outside the addressed result. -/
theorem conditionTree_evalVerdictExcept_or_value_hidesRight
    (left right : ConditionTree Source)
    (evalLeaf : Source → Except Error Verdict)
    (leftResult : left.evalVerdictExcept evalLeaf = .ok (.fired .value)) :
    (ConditionTree.or left right).evalVerdictExcept evalLeaf =
      Except.ok (.fired .value) := by
  rw [ConditionTree.evalVerdictExcept, leftResult]
  rfl

/-- Strong-Kleene validation preserves a structural failure from the right branch for every clean left truth, including false. -/
theorem conditionTree_evalKExcept_and_right_error
    (left right : ConditionTree Source)
    (evalLeaf : Source → Except Error K) (leftValue : K)
    (leftResult : left.evalKExcept evalLeaf = .ok leftValue)
    (rightResult : right.evalKExcept evalLeaf = .error cause) :
    (ConditionTree.and left right).evalKExcept evalLeaf =
      Except.error cause := by
  rw [ConditionTree.evalKExcept, leftResult, rightResult]
  rfl

/-- Computation's decisive clean false keeps an unreachable structural failure on the right outside the addressed result. -/
theorem conditionTree_evalComputationExcept_and_notTrue_hidesRight
    (left right : ConditionTree Source)
    (evalLeaf : Source → Except Error ComputationConditionResult)
    (leftResult :
      left.evalComputationExcept evalLeaf = .ok .notTrue) :
    (ConditionTree.and left right).evalComputationExcept evalLeaf =
      Except.ok .notTrue := by
  rw [ConditionTree.evalComputationExcept, leftResult]
  rfl

/-- Reusing the shared connective representation does not change any established flat verdict. -/
@[simp]
theorem validationCondition_flat_evalSelected
    (model : FlatModel) (condition : FlatCondition)
    (context : ValidationEvaluationContext)
    (isRelevant : FlatRelevance) :
    (ValidationCondition.flat (model := model) condition).evalSelected
        context isRelevant =
      condition.evalSelected context.fields isRelevant := by
  simp [ValidationCondition.flat, ValidationCondition.evalSelected,
    FlatCondition.evalSelected, ValidationConditionLeaf.evalSelected]

/-- The mixed tree's reference traversal preserves every reference in an embedded flat condition. -/
@[simp]
theorem validationCondition_flat_referencesField
    (condition : FlatCondition) (model : FlatModel) (field : FieldId) :
    (ValidationCondition.flat (model := model) condition).referencesField field =
      condition.referencesField field := by
  simp [ValidationCondition.flat, ValidationCondition.referencesField,
    FlatCondition.referencesField, ValidationConditionLeaf.referencesField]

/-- An embedded flat tree cannot acquire a synthetic filter marker. -/
@[simp]
theorem validationCondition_flat_hasHaving
    (condition : FlatCondition) (model : FlatModel) :
    (ValidationCondition.flat (model := model) condition).hasHaving = false := by
  induction condition with
  | leaf leaf =>
      simp [ValidationCondition.flat, ValidationCondition.hasHaving,
        ValidationConditionLeaf.hasHaving, ConditionTree.map,
        ConditionTree.anyLeaf]
  | and left right leftIH rightIH | or left right leftIH rightIH =>
      simp_all [ValidationCondition.flat, ValidationCondition.hasHaving,
        ConditionTree.map, ConditionTree.anyLeaf]

/-- Rule-wide filter discovery is structural and therefore traverses both sides of either connective, independently of runtime short-circuiting. -/
@[simp]
theorem validationCondition_hasHaving_and
    (left right : ValidationCondition model) :
    ValidationCondition.hasHaving (.and left right) =
      (left.hasHaving || right.hasHaving) := by
  rfl

@[simp]
theorem validationCondition_hasHaving_or
    (left right : ValidationCondition model) :
    ValidationCondition.hasHaving (.or left right) =
      (left.hasHaving || right.hasHaving) := by
  rfl

/-- A relevant checked numeric comparison evaluates exactly as its existing resolved core. -/
@[simp]
theorem validationCondition_numeric_evalSelected_of_relevant
    (model : FlatModel) (comparison : NumericComparison)
    (context : ValidationEvaluationContext)
    (isRelevant : FlatRelevance)
    (relevant : comparison.allRelevant isRelevant = true) :
    (ValidationCondition.numeric (model := model) comparison).evalSelected
        context isRelevant =
      comparison.evalSelectedWithGroups context := by
  simp [ValidationCondition.numeric, ValidationCondition.evalSelected,
    ValidationConditionLeaf.evalSelected, relevant]

/-- A reached resolved group leaf delegates exactly to the established product-state operator. -/
@[simp]
theorem validationCondition_groupPresence_evalSelected
    (model : FlatModel) (operator : GroupPresenceOperator)
    (reference : ResolvedGroupReference)
    (context : ValidationEvaluationContext) (state : GroupPresenceState)
    (resolved : context.groups reference.path = some state)
    (isRelevant : FlatRelevance) :
    (ValidationCondition.groupPresence (model := model)
        operator reference).evalSelected
        context isRelevant = operator.eval state := by
  simp [ValidationCondition.groupPresence, ValidationCondition.evalSelected,
    ValidationConditionLeaf.evalSelected, resolved]

/-- Missing checked-document group state is explicit semantic unavailability. -/
@[simp]
theorem validationCondition_groupPresence_missing_isUnknown
    (model : FlatModel) (operator : GroupPresenceOperator)
    (reference : ResolvedGroupReference)
    (context : ValidationEvaluationContext)
    (missing : context.groups reference.path = none)
    (isRelevant : FlatRelevance) :
    (ValidationCondition.groupPresence (model := model)
        operator reference).evalSelected
        context isRelevant = .unknown := by
  simp [ValidationCondition.groupPresence, ValidationCondition.evalSelected,
    ValidationConditionLeaf.evalSelected, missing]

/-- A reached fixed field/group list delegates once to the shared entity-presence tally and preserves its conservative collapsed-result embedding. -/
@[simp]
theorem validationCondition_groupList_evalSelected
    (model : FlatModel) (operator : GroupFillQuantifier)
    (operands : List ResolvedGroupListOperand)
    (context : ValidationEvaluationContext)
    (isRelevant : FlatRelevance) :
    (ValidationCondition.groupList (model := model)
        operator operands).evalSelected
        context isRelevant =
      (operator.evalPresence
        (operands.map fun operand =>
          operand.evalPresence context isRelevant)).asConservativeVerdict := by
  rfl

/-- The conservative embedding loses only the unobservable false/unknown distinction; it preserves every fired result and its exact polarity. -/
theorem validationCondition_groupList_fired_iff
    (model : FlatModel) (operator : GroupFillQuantifier)
    (operands : List ResolvedGroupListOperand)
    (context : ValidationEvaluationContext)
    (isRelevant : FlatRelevance)
    (polarity : Polarity) :
    (ValidationCondition.groupList (model := model)
        operator operands).evalSelected
        context isRelevant = .fired polarity ↔
      operator.evalPresence
        (operands.map fun operand =>
          operand.evalPresence context isRelevant) = .fired polarity := by
  rw [validationCondition_groupList_evalSelected model]
  generalize operator.evalPresence
      (List.map (fun operand =>
        operand.evalPresence context isRelevant) operands) = outcome
  cases outcome <;> simp [ValidationFillOutcome.asConservativeVerdict]

/-- An ordinary repeatable presence leaf always requires the addressed evaluator; selecting the scalar entry point cannot silently substitute UNKNOWN. -/
@[simp]
theorem validationCondition_repeatablePresence_requiresAddressed
    (model : FlatModel) (operator : RepeatableFieldPresenceOperator)
    (declaration : FlatFieldDecl) :
    (ValidationCondition.repeatableFieldPresence (model := model)
      operator declaration).requiresAddressedValidation = true := by
  rfl

/-- A selected ordinary repeatable presence leaf reads the exact current environment and delegates to the established phase observation. -/
@[simp]
theorem validationCondition_repeatablePresence_evalAddressed
    (model : FlatModel) (operator : RepeatableFieldPresenceOperator)
    (declaration : FlatFieldDecl)
    (context : AddressedValidationEvaluationContext model) :
    (ValidationCondition.repeatableFieldPresence (model := model)
      operator declaration).evalAddressed context =
      (context.readCell context.outer declaration.id).map fun cell =>
        operator.eval (observeCell .validation cell) := by
  rfl

/-- One non-starred repeatable field declaration is the sole source of its ordinary rule-iteration scope. -/
@[simp]
theorem validationCondition_repeatablePresence_iterationScope
    (model : FlatModel) (operator : RepeatableFieldPresenceOperator)
    (declaration : FlatFieldDecl) :
    (ValidationCondition.repeatableFieldPresence (model := model)
      operator declaration).ordinaryIterationScope =
      .ok (some declaration.repeatableScope) := by
  rfl

/-- The first ordinary repeatable route is closed under flat/repeatable connective composition and excludes specialized addressed leaf families. -/
@[simp]
theorem validationCondition_repeatablePresence_supported
    (model : FlatModel) (operator : RepeatableFieldPresenceOperator)
    (declaration : FlatFieldDecl) :
    (ValidationCondition.repeatableFieldPresence (model := model)
      operator declaration).supportsOrdinaryIteration = true := by
  rfl

/-- The checked mixed wrapper carries one model and exact row-group certificate for its complete resolved core. -/
theorem checkedValidationCondition_coherent
    (condition : CheckedValidationCondition model) :
    model.validate.isOk = true ∧
      condition.core.wellFormedBool condition.rowGroup = true :=
  ⟨condition.modelWellFormed, condition.wellFormed⟩

end A12Kernel
