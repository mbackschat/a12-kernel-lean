import A12Kernel.Elaboration.ValidationCondition
import A12Kernel.Proofs.GroupPresence
import A12Kernel.Proofs.ConditionTree

/-! # Shared validation-condition laws

These laws show that the shared connective tree preserves an established flat condition exactly and that embedding a checked numeric comparison adds only its relevance gate.
-/

namespace A12Kernel

@[simp]
theorem decodedNumericLiteral_negative_scale_has_no_iterationHostInt32
    (value : Rat) (scale : Int) (negative : scale < 0) :
    DecodedNumericLiteral.iterationHostInt32?
      { value, authoredScale := scale } = none := by
  simp [DecodedNumericLiteral.iterationHostInt32?,
    DecodedNumericLiteral.javaRoundedInt32?, negative]

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
    DecodedNumericLiteral.javaRoundedInt32?,
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
  have never (tree : ConditionTree FlatConditionLeaf) : tree.anyLeaf (fun _ => false) = false := by
    induction tree <;> simp_all
  unfold ValidationCondition.evalSelected ValidationCondition.evalWithTemporalResult ValidationCondition.flat
  dsimp only
  simp only [ConditionTree.evalBoolExcept_map, ConditionTree.evalClassificationExcept_map]
  dsimp only [Except.mapError, pure, Except.pure, bind, Except.bind]
  rw [ConditionTree.evalBoolExcept_pure, ConditionTree.evalClassificationExcept_pure]
  rw [conditionTree_evalVerdictExcept_embed condition ValidationConditionLeaf.flat _
    (fun leaf => (ValidationConditionLeaf.flat leaf).evalSelected context isRelevant) (fun _ => rfl)]
  rw [conditionTree_evalVerdictExcept_embed condition ValidationConditionLeaf.flat _
    (fun leaf => (ValidationConditionLeaf.flat leaf).evalSelected context isRelevant) (fun _ => rfl)]
  cases condition <;> simp [ConditionTree.map, never,
    FlatCondition.evalSelected, ValidationConditionLeaf.evalSelected]



/-- A flat leaf without repeated operands preserves the scalar evaluator even inside an addressed rule. -/
theorem validationConditionLeaf_flat_evalAddressed_scalar
    (condition : FlatConditionLeaf) (context : AddressedValidationEvaluationContext model)
    (scalar : (ValidationConditionLeaf.flat (model := model) condition).requiresAddressedValidation = false) :
    (ValidationConditionLeaf.flat condition).evalAddressed context =
      .ok (condition.evalSelected context.scalar.fields context.directRelevant) := by
  simp only [ValidationConditionLeaf.evalAddressed, scalar, Bool.not_false, ↓reduceIte]
  rfl

/-- Once row reads succeed, membership uses the established flat evaluator on exactly that row's cells. -/
theorem validationConditionLeaf_flat_evalAddressed_resolved
    (condition : FlatConditionLeaf) (context : AddressedValidationEvaluationContext model)
    (cells : List (FieldId × CheckedCell))
    (addressed : (ValidationConditionLeaf.flat (model := model) condition).requiresAddressedValidation = true)
    (resolved : ((model.fields.filter fun field =>
        condition.referencesField field.id && context.directRelevant field.id).mapM fun field => do
          pure (field.id, ← context.readCell context.outer field.id)) = .ok cells) :
    (ValidationConditionLeaf.flat condition).evalAddressed context =
      .ok (condition.evalSelected { context.scalar.fields with
        read := fun field => (cells.find? (·.1 == field)).map (·.2) |>.getD (context.scalar.fields.read field) }
        context.directRelevant) := by
  simp only [ValidationConditionLeaf.evalAddressed, addressed, Bool.not_true, ↓reduceIte, resolved]
  rfl

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
  simp [ValidationCondition.numeric, ValidationCondition.evalSelected, ValidationCondition.evalWithTemporalResult, ValidationCondition.addressedValueFailure?,
    Except.mapError,
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
  simp [ValidationCondition.groupPresence, ValidationCondition.evalSelected, ValidationCondition.evalWithTemporalResult, ValidationCondition.addressedValueFailure?,
    Except.mapError,
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
  simp [ValidationCondition.groupPresence, ValidationCondition.evalSelected, ValidationCondition.evalWithTemporalResult, ValidationCondition.addressedValueFailure?,
    Except.mapError,
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
  cases h : document.groupPresenceInput reference.path outer .fullyRelevant false <;>
    simp [ValidationCondition.groupPresence, ValidationCondition.evalAddressed,
      ValidationCondition.evalWithTemporalResult, ValidationCondition.addressedValueFailure?,
      ValidationConditionLeaf.evalAddressed, h, Except.mapError, Except.map, bind, Except.bind, pure, Except.pure]


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

/-- Partial group presence is admitted exactly because its caller must supply the relevance-selected product query. -/
@[simp]
theorem validationConditionLeaf_groupPresence_partialSupported
    (model : FlatModel) (operator : GroupPresenceOperator)
    (reference : ResolvedGroupReference) :
    (ValidationConditionLeaf.groupPresence (model := model)
      operator reference).supportsAddressedPartial = true := by
  rfl

/-- A partial group leaf delegates once to the supplied selected-slice resolver and preserves its structural error channel. -/
@[simp]
theorem validationConditionLeaf_groupPresence_partialDelegates
    (model : FlatModel) (operator : GroupPresenceOperator)
    (reference : ResolvedGroupReference)
    (context : AddressedValidationEvaluationContext model)
    (scope : ValidationRelevanceScope) (isRelevant : FlatRelevance)
    (resolveGroup :
      GroupPath → Env →
        Except CheckedAddressingError ResolvedGroupPresenceInput)
    (result? : Option RepetitionNotUniqueResult) :
    (ValidationConditionLeaf.groupPresence (model := model)
      operator reference).evalAddressedPartial?
        context scope isRelevant resolveGroup result? =
      some (do
        let input ← resolveGroup reference.path context.outer
        pure (operator.eval input.derive)) := by
  rfl

/-- An ordinary repeatable presence leaf always requires the addressed evaluator; selecting the scalar entry point cannot silently substitute UNKNOWN. -/
@[simp]
theorem validationCondition_repeatablePresence_requiresAddressed
    (model : FlatModel) (operator : RepeatableFieldPresenceOperator)
    (declaration : FlatFieldDecl) :
    (ValidationCondition.repeatableFieldPresence (model := model)
      operator declaration).requiresAddressedValidation = true := by
  rfl

/-- A selected presence leaf reads its current environment. The rule handler preserves structural
errors and classifies an explicit runtime value failure supplied by the addressed read channel. -/
@[simp]
theorem validationCondition_repeatablePresence_evalAddressed
    (model : FlatModel) (operator : RepeatableFieldPresenceOperator)
    (declaration : FlatFieldDecl)
    (context : AddressedValidationEvaluationContext model) :
    (ValidationCondition.repeatableFieldPresence (model := model)
      operator declaration).evalAddressed context =
      (match context.readCell context.outer declaration.id with
      | .ok cell => .ok (operator.eval (observeCell .validation cell))
      | .error error => if (ValidationCondition.addressedValueFailure? error).isSome then
          .ok (.fired .value) else .error error) := by
  cases h : context.readCell context.outer declaration.id with
  | ok cell => simp [ValidationCondition.repeatableFieldPresence, ValidationCondition.evalAddressed,
      ValidationCondition.evalWithTemporalResult, ValidationConditionLeaf.evalAddressed,
      h, Except.mapError, Except.map, bind, Except.bind, pure, Except.pure]
  | error error =>
      cases error <;> simp [ValidationCondition.repeatableFieldPresence, ValidationCondition.evalAddressed,
        ValidationCondition.evalWithTemporalResult, ValidationCondition.addressedValueFailure?,
        ValidationConditionLeaf.evalAddressed, h, Except.mapError, Except.map, bind, Except.bind, pure, Except.pure]
      all_goals
        rename_i cause
        cases cause <;> rfl


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

/-- Checked RNU depth changes only the existing bound-prefix partition; every source consumes the complete ordinary rule environment. -/
@[simp]
theorem validationCondition_repetitionNotUnique_ordinarySupported
    (model : FlatModel)
    (source : CheckedRepetitionNotUniqueSource model) :
    (ValidationCondition.repetitionNotUnique source).supportsOrdinaryIteration =
      true := by
  rfl

/-- Partial RNU uses the same checked topology at every depth and applies relevance before each composite-key read. -/
@[simp]
theorem validationConditionLeaf_repetitionNotUnique_partialSupported
    (model : FlatModel)
    (source : CheckedRepetitionNotUniqueSource model) :
    (ValidationConditionLeaf.repetitionNotUnique source).supportsAddressedPartial =
      true := by
  rfl

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
    ValidationCondition.evalAddressedWithRepetitionNotUnique, ValidationCondition.evalWithTemporalResult, ValidationCondition.addressedValueFailure?,
    Except.mapError, pure, Except.pure,
    ValidationConditionLeaf.evalAddressedWithRepetitionNotUnique,
    sameRow]

/-- Partial RNU treats an absent prepared result as semantic UNKNOWN because incomplete key relevance excluded the current row; a supplied result still must belong to that exact row. -/
@[simp]
theorem validationConditionLeaf_repetitionNotUnique_partialResult
    (model : FlatModel)
    (source : CheckedRepetitionNotUniqueSource model)
    (context : AddressedValidationEvaluationContext model)
    (scope : ValidationRelevanceScope)
    (isRelevant : FlatRelevance)
    (resolveGroup :
      GroupPath → Env →
        Except CheckedAddressingError ResolvedGroupPresenceInput)
    (result? : Option RepetitionNotUniqueResult) :
    (ValidationConditionLeaf.repetitionNotUnique source).evalAddressedPartial?
        context scope isRelevant resolveGroup result? =
      some (match result? with
        | some result =>
            if result.row == context.outer then
              pure result.verdict
            else
              .error (.repetitionNotUniqueResult context.outer)
        | none => pure .unknown) := by
  rfl

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

/-- Ordinary repeatable execution is closed under flat/repeatable connective composition and excludes specialized addressed leaf families. -/
@[simp]
theorem validationCondition_repeatablePresence_supported
    (model : FlatModel) (operator : RepeatableFieldPresenceOperator)
    (declaration : FlatFieldDecl) :
    (ValidationCondition.repeatableFieldPresence (model := model)
      operator declaration).supportsOrdinaryIteration = true := by
  rfl

/-- The checked mixed wrapper certifies its complete core against both execution binding and lexical origin. -/
theorem checkedValidationCondition_coherent
    (condition : CheckedValidationCondition model) :
    model.validate.isOk = true ∧
      condition.core.wellFormedBool condition.rowGroup condition.declaringGroup = true :=
  ⟨condition.modelWellFormed, condition.wellFormed⟩

/-- Rebinding supplies an execution scope without changing the resolved expression or its lexical
origin, so consumers can transport the same evaluation and reference queries through this boundary. -/
theorem checkedValidationCondition_atBinding_preserves
    (condition rebound : CheckedValidationCondition model) (group : GroupPath)
    (admitted : condition.atBinding group = .ok rebound) :
    rebound.core = condition.core ∧ rebound.declaringGroup = condition.declaringGroup ∧
      rebound.rowGroup = group := by
  unfold CheckedValidationCondition.atBinding CheckedValidationCondition.checkCore at admitted
  split at admitted
  · cases admitted
    exact ⟨rfl, rfl, rfl⟩
  · cases admitted

/-- A static cross-root dependency removes the full-validation content prerequisite, independently
of the runtime context and without changing the connective evaluator. -/
theorem validationCondition_evalFull_of_multipleRoots
    (condition : ValidationCondition model) (context : ValidationEvaluationContext)
    (hasContent : Bool) (spans : condition.referencesMultipleRoots = true) :
    condition.evalFull context hasContent = condition.evalSelected context := by
  simp [ValidationCondition.evalFull, ValidationCondition.canFireOnEmpty, spans]

/-- The same root classification preserves the addressed evaluator's structural error channel. -/
theorem validationCondition_evalAddressedFull_of_multipleRoots
    (condition : ValidationCondition model) (context : AddressedValidationEvaluationContext model)
    (hasContent : Bool) (spans : condition.referencesMultipleRoots = true) :
    condition.evalAddressedFull context hasContent = condition.evalAddressed context := by
  simp [ValidationCondition.evalAddressedFull, ValidationCondition.canFireOnEmpty, spans]

end A12Kernel
