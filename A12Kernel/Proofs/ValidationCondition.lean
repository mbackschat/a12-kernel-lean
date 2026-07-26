import A12Kernel.Elaboration.ValidationCondition
import A12Kernel.Proofs.GroupPresence

/-! # Shared validation-condition laws

These laws show that the shared connective tree preserves an established flat condition exactly and that embedding a checked numeric comparison adds only its relevance gate.
-/

namespace A12Kernel

@[simp]
theorem decodedNumericLiteral_negative_scale_has_no_iterationHostInt32
    (value : Rat) (scale : Int) (negative : scale < 0) :
    DecodedNumericLiteral.iterationHostInt32?
      { value, authoredScale := scale } = none := by
  simp [DecodedNumericLiteral.iterationHostInt32?, negative]

/-- Once both checked scales certify the same finite decimal value, redundant trailing-zero spelling cannot change the kernel host integer. -/
theorem decodedNumericLiteral_iterationHostInt32_scale_invariant
    (value : Rat) (leftScale rightScale : Int)
    (leftNonnegative : 0 ≤ leftScale)
    (rightNonnegative : 0 ≤ rightScale)
    (leftDecimal :
      (value * (10 ^ leftScale.toNat : Nat)).den = 1)
    (rightDecimal :
      (value * (10 ^ rightScale.toNat : Nat)).den = 1) :
    DecodedNumericLiteral.iterationHostInt32? {
        value, authoredScale := leftScale
      } =
      DecodedNumericLiteral.iterationHostInt32? {
        value, authoredScale := rightScale
      } := by
  simp only [DecodedNumericLiteral.iterationHostInt32?,
    Int.not_lt.mpr leftNonnegative, Int.not_lt.mpr rightNonnegative,
    leftDecimal, rightDecimal, ↓reduceIte]

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

/-- One guarded conjunct is sufficient at the queried repeatable level, independently of the other conjunct's classification. -/
theorem conditionTree_iterationGuardStatus_and_guarded_left
    (left right : ConditionTree Source)
    (classify : Source → IterationGuardStatus)
    (guarded : left.iterationGuardStatus classify = .guarded) :
    (ConditionTree.and left right).iterationGuardStatus classify =
      .guarded := by
  simp [ConditionTree.iterationGuardStatus, guarded,
    IterationGuardStatus.and]

/-- A disjunction is guarded at one repeatable level exactly when both branches independently reference and guard that level. -/
theorem conditionTree_iterationGuardStatus_or_guarded_iff
    (left right : ConditionTree Source)
    (classify : Source → IterationGuardStatus) :
    (ConditionTree.or left right).iterationGuardStatus classify =
        .guarded ↔
      left.iterationGuardStatus classify = .guarded ∧
        right.iterationGuardStatus classify = .guarded := by
  change IterationGuardStatus.or _ _ = .guarded ↔ _
  generalize left.iterationGuardStatus classify = leftStatus
  generalize right.iterationGuardStatus classify = rightStatus
  cases leftStatus <;> cases rightStatus <;> decide

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

/-- A group reference contributes exactly its model-owned repeatable ancestry to ordinary rule iteration, and the same fact selects the addressed evaluator. -/
theorem validationCondition_groupPresence_addressingPolicy
    (model : FlatModel) (operator : GroupPresenceOperator)
    (reference : ResolvedGroupReference) :
    (ValidationCondition.groupPresence (model := model)
      operator reference).ordinaryIterationScope =
        .ok (let scope := model.repeatableScopeForGroupPath reference.path
          if scope.isEmpty then none else some scope) ∧
      (ValidationCondition.groupPresence (model := model)
        operator reference).requiresAddressedValidation =
          !(model.repeatableScopeForGroupPath reference.path).isEmpty := by
  exact ⟨rfl, rfl⟩

/-- Group presence contributes its positive/negative static guard at every model-owned repeatable ancestor and nowhere else. -/
theorem validationCondition_groupPresence_iterationGuardStatusAt
    (model : FlatModel) (operator : GroupPresenceOperator)
    (reference : ResolvedGroupReference) (level : RepeatableLevel) :
    (ValidationCondition.groupPresence (model := model)
      operator reference).iterationGuardStatusAt level =
        if (model.repeatableScopeForGroupPath reference.path).contains level then
          match operator with
          | .filled => .guarded
          | .notFilled => .unguarded
        else .noReference := by
  rfl

/-- The ordinary repeatable rule route consumes group presence through its existing checked product owner. -/
@[simp]
theorem validationCondition_groupPresence_evalAddressed_checked
    (model : FlatModel) (operator : GroupPresenceOperator)
    (reference : ResolvedGroupReference)
    (scalar : ValidationEvaluationContext) (outer : Env)
    (document : CheckedDocument model) :
    (ValidationCondition.groupPresence (model := model)
      operator reference).evalAddressed {
        scalar, outer, input := .checked document
      } =
        ((document.groupPresenceInput reference.path outer
          .fullyRelevant false).mapError CheckedAddressingError.group).map
            fun input => operator.eval input.derive := by
  rfl

/-- A structural group-slice failure remains in the addressed error channel and cannot become semantic UNKNOWN. -/
theorem validationCondition_groupPresence_addressError
    (model : FlatModel) (operator : GroupPresenceOperator)
    (reference : ResolvedGroupReference)
    (scalar : ValidationEvaluationContext) (outer : Env)
    (document : CheckedDocument model)
    (fails : document.groupPresenceInput reference.path outer
      .fullyRelevant false = .error cause) :
    (ValidationCondition.groupPresence (model := model)
      operator reference).evalAddressed {
        scalar, outer, input := .checked document
      } =
        .error (.group cause) := by
  rw [validationCondition_groupPresence_evalAddressed_checked
    model operator reference scalar outer document, fails]
  rfl

/-- Scalar evaluation delegates a wholly direct field/group list to the shared entity-presence tally and refuses every list that still needs starred topology. -/
@[simp]
theorem validationCondition_groupList_evalSelected
    (model : FlatModel) (operator : GroupFillQuantifier)
    (operands : List (ResolvedGroupListOperand model))
    (context : ValidationEvaluationContext)
    (isRelevant : FlatRelevance) :
    (ValidationCondition.groupList (model := model)
        operator operands).evalSelected
        context isRelevant =
      match operands.mapM fun operand =>
          operand.evalDirectPresence? context isRelevant with
      | some states =>
          (operator.evalPresence states).asConservativeVerdict
      | none => .unknown := by
  rfl

/-- Scalar group-list evaluation fires exactly when every operand is direct and the shared tally fires with the same polarity. -/
theorem validationCondition_groupList_fired_iff
    (model : FlatModel) (operator : GroupFillQuantifier)
    (operands : List (ResolvedGroupListOperand model))
    (context : ValidationEvaluationContext)
    (isRelevant : FlatRelevance)
    (states : List GroupListPresenceState)
    (direct : operands.mapM (fun operand =>
      operand.evalDirectPresence? context isRelevant) = some states)
    (polarity : Polarity) :
    (ValidationCondition.groupList (model := model)
        operator operands).evalSelected
        context isRelevant = .fired polarity ↔
      operator.evalPresence states = .fired polarity := by
  rw [validationCondition_groupList_evalSelected model, direct]
  exact validationFillOutcome_conservative_fired_iff
    (operator.evalPresence states) polarity

/-- A nonrepeatable terminal below starred ancestry consumes the canonical topology and classifies each concrete environment through the existing checked group-product owner. -/
theorem resolvedGroupListOperand_starredGroupPresence_checked
    (model : FlatModel)
    (source : CheckedStarredGroupPresenceSource model)
    (scalar : ValidationEvaluationContext) (outer : Env)
    (document : CheckedDocument model) :
    (ResolvedGroupListOperand.starredGroupPresence source).evalAddressedTally {
        scalar, outer, input := .checked document
      } = (do
        let topology ←
          (source.resolvedTopology document.source.toDocument outer)
            |>.mapError CheckedAddressingError.addressing
        let states ← topology.environments.mapM fun environment => do
          let input ←
            (document.groupPresenceInput source.groupPath environment
              .fullyRelevant false).mapError CheckedAddressingError.group
          pure input.derive.asGroupListPresence
        pure (GroupListPresenceTally.ofStates states)) := by
  rfl

/-- The legacy addressed context cannot manufacture descendant-derived group products; that missing checked-document boundary remains structural rather than semantic UNKNOWN. -/
@[simp] theorem resolvedGroupListOperand_starredGroupPresence_legacy
    (model : FlatModel)
    (source : CheckedStarredGroupPresenceSource model)
    (scalar : ValidationEvaluationContext) (outer : Env)
    (document : Document) (read : Env → FieldId → CheckedCell) :
    (ResolvedGroupListOperand.starredGroupPresence source).evalAddressedTally {
        scalar, outer, input := .legacy document read
      } = .error (.checkedDocumentRequired source.groupPath) := by
  rfl

/-- A group-list leaf requires the addressed evaluator exactly when one checked starred group source remains in its operand list. -/
@[simp]
theorem validationCondition_groupList_requiresAddressed
    (model : FlatModel) (operator : GroupFillQuantifier)
    (operands : List (ResolvedGroupListOperand model)) :
    (ValidationCondition.groupList (model := model)
      operator operands).requiresAddressedValidation =
        operands.any ResolvedGroupListOperand.isStarred := by
  rfl

/-- Addressed group-list evaluation combines each direct classification and starred terminal contribution once, then delegates to the established tally table. -/
@[simp]
theorem validationCondition_groupList_evalAddressed
    (model : FlatModel) (operator : GroupFillQuantifier)
    (operands : List (ResolvedGroupListOperand model))
    (context : AddressedValidationEvaluationContext model) :
    (ValidationCondition.groupList (model := model)
        operator operands).evalAddressed context =
      (ResolvedGroupListOperands.evalAddressedTally context operands).map
        fun tally =>
          (operator.evalTally tally).asConservativeVerdict := by
  rfl

/-- A reached topology or document failure stays in the structural error channel and cannot become semantic UNKNOWN. -/
theorem validationCondition_groupList_addressing_failure
    (model : FlatModel) (operator : GroupFillQuantifier)
    (operands : List (ResolvedGroupListOperand model))
    (context : AddressedValidationEvaluationContext model)
    (cause : CheckedAddressingError)
    (fails : ResolvedGroupListOperands.evalAddressedTally
      context operands = .error cause) :
    (ValidationCondition.groupList (model := model)
      operator operands).evalAddressed context = .error cause := by
  rw [validationCondition_groupList_evalAddressed, fails]
  rfl

/-- A group-list leaf exposes exactly the captured prefix of its checked starred operands as its ordinary rule-iteration scope. -/
@[simp]
theorem validationCondition_groupList_iterationScope
    (model : FlatModel) (operator : GroupFillQuantifier)
    (operands : List (ResolvedGroupListOperand model)) :
    (ValidationCondition.groupList (model := model)
      operator operands).ordinaryIterationScope =
        ValidationCondition.ResolvedGroupListOperands.iterationScope operands := by
  rfl

/-- The group-list leaf delegates its level-local static classification to the source-faithful positive/negative list rule. -/
@[simp]
theorem validationCondition_groupList_iterationGuardStatusAt
    (model : FlatModel) (operator : GroupFillQuantifier)
    (operands : List (ResolvedGroupListOperand model))
    (level : RepeatableLevel) :
    (ValidationCondition.groupList (model := model)
      operator operands).iterationGuardStatusAt level =
        ValidationCondition.ResolvedGroupListOperands.iterationGuardAt
          operator operands level := by
  rfl

/-- A negative starred group list is unguarded exactly at levels referenced by at least one captured operand prefix. -/
theorem resolvedGroupListOperands_noGroupFilled_unguarded_iff
    (operands : List (ResolvedGroupListOperand model))
    (level : RepeatableLevel) :
    ValidationCondition.ResolvedGroupListOperands.iterationGuardAt
        .noGroupFilled operands level = .unguarded ↔
      (operands.map fun operand =>
        match ResolvedGroupListOperand.iterationScope operand with
        | some scope => scope.contains level
        | none => false).any id = true := by
  let references := operands.map fun operand =>
    match ResolvedGroupListOperand.iterationScope operand with
    | some scope => scope.contains level
    | none => false
  change
    (if !references.any id then IterationGuardStatus.noReference
      else IterationGuardStatus.unguarded) =
        IterationGuardStatus.unguarded ↔
      references.any id = true
  cases references.any id <;> simp

/-- A positive starred group list guards exactly when some operand references the level and every operand does. -/
theorem resolvedGroupListOperands_atLeastOneGroupFilled_guarded_iff
    (operands : List (ResolvedGroupListOperand model))
    (level : RepeatableLevel) :
    ValidationCondition.ResolvedGroupListOperands.iterationGuardAt
        .atLeastOneGroupFilled operands level = .guarded ↔
      let references := operands.map fun operand =>
        match ResolvedGroupListOperand.iterationScope operand with
        | some scope => scope.contains level
        | none => false
      references.any id = true ∧ references.all id = true := by
  let references := operands.map fun operand =>
    match ResolvedGroupListOperand.iterationScope operand with
    | some scope => scope.contains level
    | none => false
  change
    (if !references.any id then IterationGuardStatus.noReference
      else if references.all id then IterationGuardStatus.guarded
      else IterationGuardStatus.unguarded) =
        IterationGuardStatus.guarded ↔
      references.any id = true ∧ references.all id = true
  cases references.any id <;>
    cases references.all id <;>
    simp

/-- Every checked group-list leaf can use the ordinary addressed evaluator; elaboration already excludes unsupported starred/operator combinations. -/
@[simp]
theorem validationCondition_groupList_supported
    (model : FlatModel) (operator : GroupFillQuantifier)
    (operands : List (ResolvedGroupListOperand model)) :
    (ValidationCondition.groupList (model := model)
      operator operands).supportsOrdinaryIteration = true := by
  rfl

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

/-- Repeatable field presence contributes its positive/negative static guard at every declared repeatable ancestor and nowhere else. -/
theorem validationCondition_repeatablePresence_iterationGuardStatusAt
    (model : FlatModel) (operator : RepeatableFieldPresenceOperator)
    (declaration : FlatFieldDecl) (level : RepeatableLevel) :
    (ValidationCondition.repeatableFieldPresence (model := model)
      operator declaration).iterationGuardStatusAt level =
        if declaration.repeatableScope.contains level then
          match operator with
          | .filled => .guarded
          | .notFilled => .unguarded
        else .noReference := by
  rfl

/-- One checked RNU source always selects the addressed evaluator and contributes its model-owned key declarations to ordinary row reads. -/
theorem validationCondition_repetitionNotUnique_addressingPolicy
    (model : FlatModel)
    (source : CheckedRepetitionNotUniqueSource model) :
    (ValidationCondition.repetitionNotUnique source).requiresAddressedValidation =
        true ∧
      (ValidationCondition.repetitionNotUnique source).ordinaryRepeatableFields =
        source.keys.map fun key => key.source.declaration := by
  exact ⟨rfl, rfl⟩

/-- Mixed-condition traversal delegates RNU reference membership to the checked source that retains the authored-`@From` distinction. -/
@[simp]
theorem validationCondition_repetitionNotUnique_referencesField
    (model : FlatModel)
    (source : CheckedRepetitionNotUniqueSource model)
    (field : FieldId) :
    (ValidationCondition.repetitionNotUnique source).referencesField field =
      source.referencesField field := by
  rfl

/-- A prepared current-row RNU result enters the shared connective evaluator unchanged; a row mismatch remains a structural failure. -/
theorem validationCondition_repetitionNotUnique_preparedResult
    (model : FlatModel)
    (source : CheckedRepetitionNotUniqueSource model)
    (context : AddressedValidationEvaluationContext model)
    (result : RepetitionNotUniqueResult) :
    (ValidationCondition.repetitionNotUnique source).evalAddressedWithRepetitionNotUnique
        context (some result) =
      if result.row == context.outer then
        (pure result.verdict : Except CheckedAddressingError Verdict)
      else
        .error (.repetitionNotUniqueResult context.outer) := by
  by_cases sameRow : result.row = context.outer <;>
    simp [ValidationCondition.repetitionNotUnique,
    ValidationCondition.evalAddressedWithRepetitionNotUnique,
    ValidationConditionLeaf.evalAddressedWithRepetitionNotUnique,
    ConditionTree.evalVerdictExcept, sameRow]

/-- At a singleton ordinary scope, one source-classified unguarded condition becomes the exact static rejection level. -/
theorem validationCondition_iterationLegality_singleton_unguarded
    (condition : ValidationCondition model) (level : RepeatableLevel)
    (scope :
      condition.ordinaryIterationScope = .ok (some [level]))
    (unguarded :
      condition.iterationGuardStatusAt level = .unguarded) :
    condition.iterationLegality = .ok (.invalid level) := by
  rw [ValidationCondition.iterationLegality, scope]
  change Except.ok
    (match condition.iterationGuardStatusAt level with
    | .guarded => ValidationCondition.IterationLegality.legal
    | .unguarded =>
        ValidationCondition.IterationLegality.invalid level
    | .noReference | .unclassified =>
        ValidationCondition.IterationLegality.insufficient level) =
      .ok (ValidationCondition.IterationLegality.invalid level)
  rw [unguarded]

/-- The same singleton route is legal when its complete tree supplies a source-classified guard at that level. -/
theorem validationCondition_iterationLegality_singleton_guarded
    (condition : ValidationCondition model) (level : RepeatableLevel)
    (scope :
      condition.ordinaryIterationScope = .ok (some [level]))
    (guarded :
      condition.iterationGuardStatusAt level = .guarded) :
    condition.iterationLegality = .ok .legal := by
  rw [ValidationCondition.iterationLegality, scope]
  change Except.ok
    (match condition.iterationGuardStatusAt level with
    | .guarded => ValidationCondition.IterationLegality.legal
    | .unguarded =>
        ValidationCondition.IterationLegality.invalid level
    | .noReference | .unclassified =>
        ValidationCondition.IterationLegality.insufficient level) =
      .ok ValidationCondition.IterationLegality.legal
  rw [guarded]

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
