import A12Kernel.Elaboration.ValidationRule

/-! # Whole-rule and checked-assembly laws -/

namespace A12Kernel

/-- A configured provider result has priority even when it is the empty string. -/
theorem messageName_provider_wins (providerResult : String)
    (modelLabel : Option String) (debugDisplay : String) :
    ({ providerResult := some providerResult, modelLabel, debugDisplay } :
      MessageNameInput).resolve = providerResult := by
  rfl

/-- Without a provider result, a missing or empty model label uses the debug representation. -/
theorem messageName_missingOrEmptyModelLabel_usesDebug (debugDisplay : String) :
    ({ providerResult := none, modelLabel := none, debugDisplay } :
        MessageNameInput).resolve = debugDisplay ∧
      ({ providerResult := none, modelLabel := some "", debugDisplay } :
        MessageNameInput).resolve = debugDisplay := by
  simp [MessageNameInput.resolve]

/-- Without a provider result, a nonempty model label has priority over the debug representation. -/
theorem messageName_nonemptyModelLabel_wins (modelLabel debugDisplay : String)
    (nonempty : modelLabel.isEmpty = false) :
    ({ providerResult := none, modelLabel := some modelLabel, debugDisplay } :
      MessageNameInput).resolve = modelLabel := by
  simp [MessageNameInput.resolve, nonempty]

/-- A missing or explicitly empty display value selects the exact format-supplied default. -/
theorem messageValue_missingOrEmpty_usesDefault (defaultDisplay : String) :
    ({ displayValue := none, defaultDisplay } : MessageValueInput).resolve =
        defaultDisplay ∧
      ({ displayValue := some "", defaultDisplay } : MessageValueInput).resolve =
        defaultDisplay := by
  simp [MessageValueInput.resolve]

/-- Rendering adjacent structured sequences is the same as concatenating their rendered text. -/
theorem messageRenderText_append (left right : List MessageRenderPart) :
    MessageRenderPlan.renderText (left ++ right) =
      MessageRenderPlan.renderText left ++
        MessageRenderPlan.renderText right := by
  induction left with
  | nil => rfl
  | cons part rest ih =>
      simp only [List.cons_append, MessageRenderPlan.renderText, ih,
        String.append_assoc]

/-- A nonempty display string is opaque replacement data, including token-looking bytes. -/
theorem messageValue_present_isOpaque (value defaultDisplay : String)
    (nonempty : value.isEmpty = false) :
    (MessageRenderPart.fieldValue {
      displayValue := some value
      defaultDisplay
    }).render = value := by
  simp [MessageRenderPart.render, MessageValueInput.resolve, nonempty]

/-- Resolving an unmatched message address cannot change the condition's verdict. -/
@[simp] theorem resolvedRule_emitAtCoordinates_verdict (rule : ResolvedRule Condition)
    (coordinates : List MessageRepetitionCoordinate) (verdict : Verdict) :
    (rule.emitAtCoordinates coordinates verdict).verdict = verdict := by
  cases verdict <;> rfl

/-- Existing physical emission is exactly the concrete-coordinate specialization. -/
theorem resolvedRule_emitAtCoordinates_concrete (rule : ResolvedRule Condition)
    (path : List Nat) (verdict : Verdict) :
    rule.emitAtCoordinates (path.map .concrete) verdict = rule.emitAt path verdict := rfl

/-- The addressed emitter preserves the exact verdict while changing only metadata on a firing. -/
@[simp]
theorem resolvedRule_emitAt_verdict (rule : ResolvedRule Condition)
    (errorPath : List Nat) (verdict : Verdict) :
    (rule.emitAt errorPath verdict).verdict = verdict :=
  resolvedRule_emitAtCoordinates_verdict rule (errorPath.map .concrete) verdict

/-- A firing carries the caller-resolved path through the sole emitter unchanged. -/
@[simp]
theorem resolvedRule_emitAt_fired_exact (rule : ResolvedRule Condition)
    (errorPath : List Nat) (messageType : Polarity) :
    rule.emitAt errorPath (.fired messageType) =
      .fired {
        errorAddress := { entity := rule.errorEntity, coordinates := errorPath.map .concrete }
        errorCode := rule.errorCode
        severity := rule.severity
        messageType
        text := rule.messagePlan.render
      } := by
  rfl

/-- Forgetting emitted metadata recovers exactly the verdict of the reused condition evaluator. -/
theorem resolvedRule_evalWith_verdict (rule : ResolvedRule Condition)
    (evaluate : Condition → Verdict) :
    (rule.evalWith evaluate).verdict = evaluate rule.condition := by
  simp [ResolvedRule.evalWith, ResolvedRule.evalWithAt]

/-- Forgetting emitted metadata recovers exactly the verdict of the reused flat condition evaluator. -/
theorem flatRule_eval_verdict (rule : ResolvedFlatRule)
    (context : FlatContext) (hasContent : Bool) :
    (rule.evalFull context hasContent).verdict =
      rule.condition.evalFull context hasContent := by
  exact resolvedRule_evalWith_verdict rule
    (fun condition => condition.evalFull context hasContent)

/-- The mixed specialization uses the same post-verdict boundary without changing its condition result. -/
theorem validationRule_eval_verdict (rule : ResolvedValidationRule model)
    (context : ValidationEvaluationContext) (hasContent : Bool) :
    (ResolvedValidationRule.evalFull rule context hasContent).verdict =
      rule.condition.evalFull context hasContent := by
  unfold ResolvedValidationRule.evalFull ValidationCondition.evalFull
  split
  · cases h : rule.condition.evalSelectedResult context with
    | ok verdict =>
        simp [ResolvedValidationRule.emitEvaluationResult, ValidationCondition.evalSelected,
          h, Except.toOption, ResolvedRule.emit]
    | error fault =>
        simp [ResolvedValidationRule.emitEvaluationResult, ValidationCondition.evalSelected,
          h, Except.toOption, ResolvedRule.emitRuntimeFailureAt, ResolvedRule.emitAt,
          ResolvedRule.emitAtCoordinates, FlatRuleOutcome.verdict]
  · rfl

/-- A fired condition copies the exact resolved address and supplied metadata, renders the structured plan, and derives its message type from the verdict. -/
theorem flatRule_fired_message_exact (rule : ResolvedFlatRule)
    (context : FlatContext) (hasContent : Bool) (messageType : Polarity)
    (fires : rule.condition.evalFull context hasContent = .fired messageType) :
    rule.evalFull context hasContent =
      .fired {
        errorAddress := { entity := rule.errorEntity, coordinates := [] }
        errorCode := rule.errorCode
        severity := rule.severity
        messageType
        text := rule.messagePlan.render
  } := by
  simp [ResolvedRule.evalFull, ResolvedRule.evalWith,
    ResolvedRule.evalWithAt, ResolvedRule.emitAt, ResolvedRule.emitAtCoordinates, fires]

/-- Error address, code, severity, and already-resolved text cannot change firing or polarity. -/
theorem flatRule_metadata_doesNotChangeVerdict (rule : ResolvedFlatRule)
    (errorEntity : RuleErrorEntity) (errorCode : String)
    (severity : ValidationSeverity)
    (messagePlan : MessageRenderPlan)
    (context : FlatContext) (hasContent : Bool) :
    (({ rule with errorEntity, errorCode, severity, messagePlan }).evalFull
        context hasContent).verdict =
      (rule.evalFull context hasContent).verdict := by
  rw [flatRule_eval_verdict, flatRule_eval_verdict]

/-- A clean non-firing condition makes the whole-rule result independent of every structured message input. -/
theorem flatRule_notFired_independentOfMessagePlan
    (rule : ResolvedFlatRule) (otherPlan : MessageRenderPlan)
    (context : FlatContext) (hasContent : Bool)
    (notFired : rule.condition.evalFull context hasContent = .notFired) :
    ({ rule with messagePlan := otherPlan }).evalFull context hasContent =
      rule.evalFull context hasContent := by
  simp [ResolvedRule.evalFull, ResolvedRule.evalWith,
    ResolvedRule.evalWithAt, ResolvedRule.emitAt, ResolvedRule.emitAtCoordinates, notFired]

/-- An unavailable condition likewise suppresses message resolution rather than manufacturing text. -/
theorem flatRule_unknown_independentOfMessagePlan
    (rule : ResolvedFlatRule) (otherPlan : MessageRenderPlan)
    (context : FlatContext) (hasContent : Bool)
    (unknown : rule.condition.evalFull context hasContent = .unknown) :
    ({ rule with messagePlan := otherPlan }).evalFull context hasContent =
      rule.evalFull context hasContent := by
  simp [ResolvedRule.evalFull, ResolvedRule.evalWith,
    ResolvedRule.evalWithAt, ResolvedRule.emitAt, ResolvedRule.emitAtCoordinates, unknown]

/-- A rule carries a message exactly when the reused condition evaluator fired. -/
theorem flatRule_hasMessage_iff_fired (rule : ResolvedFlatRule)
    (context : FlatContext) (hasContent : Bool) :
    (rule.evalFull context hasContent).message?.isSome = true ↔
      ∃ messageType, rule.condition.evalFull context hasContent = .fired messageType := by
  rw [← flatRule_eval_verdict]
  generalize outcomeEq : rule.evalFull context hasContent = outcome
  cases outcome <;> simp [FlatRuleOutcome.message?, FlatRuleOutcome.verdict]

/-- Only ERROR severity invalidates; message emission itself is independent of this test. -/
theorem flatRuleMessage_invalidates_iff_error (message : FlatRuleMessage) :
    message.invalidates = true ↔ message.severity = .error := by
  cases severityEq : message.severity <;>
    simp [FlatRuleMessage.invalidates, severityEq]

/-- Observable silence alone cannot recover the internal rule verdict. -/
theorem equal_flatRuleSilence_doesNotImply_equalVerdict :
    FlatRuleOutcome.notFired.message? = FlatRuleOutcome.unknown.message? ∧
      FlatRuleOutcome.notFired.verdict ≠ FlatRuleOutcome.unknown.verdict := by
  decide

/-- Flat checked assembly carries one unique, nonrepeatable, referenced error field from the same model as the condition: a flat condition references no group, so a flat rule never reports on one. -/
theorem checkedFlatRule_errorField_coherent
    (rule : CheckedResolvedFlatRule model) :
    ∃ field declaration, rule.errorEntity = .field field ∧
      rule.errorPlacement = .field declaration ∧
      model.lookupUniqueId field = .ok declaration ∧
      declaration.repeatableScope.isEmpty = true ∧
      rule.condition.core.referencesField field = true :=
  by
    have noScope : rule.iterationScope = none := by
      simpa using rule.iterationScopeOwned.symm
    have scope := rule.errorEntityScopeCompatible
    have owned := rule.errorPlacementOwned
    have referenced := rule.errorEntityReferenced
    rw [noScope] at scope
    generalize rule.errorEntity = entity at owned referenced ⊢
    generalize rule.errorPlacement = placement at owned scope ⊢
    cases entity with
    | group path => simp [FlatCondition.referencesErrorEntity] at referenced
    | field field =>
        simp only [FlatModel.ruleErrorPlacement] at owned
        split at owned
        · rename_i declaration lookup
          cases owned
          exact ⟨field, declaration, rfl, rfl, lookup,
            by simpa [ruleErrorScopeCompatible, RuleErrorPlacement.repeatableScope] using scope,
            by simpa [FlatCondition.referencesErrorEntity] using referenced⟩
        · cases owned

/-- Mixed checked assembly certifies the exact error placement, its derived ordinary iteration
scope, and a reference to the error entity: for a field, outside every filter body or marked inside
one; for a group, a presence of it or of a group containing it. -/
theorem checkedValidationRule_errorEntity_coherent
    (rule : CheckedResolvedValidationRule model) :
    model.ruleErrorPlacement rule.errorEntity = .ok rule.errorPlacement ∧
      ruleErrorScopeCompatible true
        rule.errorPlacement.repeatableScope rule.iterationScope = true ∧
      rule.condition.core.referencesErrorEntity rule.errorEntity = true :=
  ⟨rule.errorPlacementOwned, rule.errorEntityScopeCompatible,
    rule.errorEntityReferenced⟩

/-- Error addressing retains the resolved iteration prefix and defaults only its remaining suffix. -/
theorem checkedValidationRule_errorPathAt_resolved
    (rule : CheckedResolvedValidationRule model) (environment : Env) (bound : List Nat)
    (resolved : environment.pathForScope (rule.iterationScope.getD []) = .ok bound) :
    rule.errorPathAt environment = .ok
      (bound ++ List.replicate (rule.errorPlacement.repeatableScope.length - bound.length) 1) := by
  simp only [CheckedResolvedValidationRule.errorPathAt, resolved]
  rfl

/-- Pinning error-only levels cannot replace a condition-bound coordinate. -/
theorem checkedValidationRule_errorPathAt_preserves_bound
    (rule : CheckedResolvedValidationRule model) (environment : Env) (bound : List Nat)
    (resolved : environment.pathForScope (rule.iterationScope.getD []) = .ok bound) :
    (rule.errorPathAt environment).map (List.take bound.length) = .ok bound := by
  rw [checkedValidationRule_errorPathAt_resolved rule environment bound resolved]
  change .ok ((bound ++ List.replicate
    (rule.errorPlacement.repeatableScope.length - bound.length) 1).take bound.length) = Except.ok bound
  simp

/-- Checked assembly cannot substitute a caller-selected ordinary iteration scope for the one derived from the complete checked condition tree. -/
theorem checkedValidationRule_iterationScope_owned
    (rule : CheckedResolvedValidationRule model) :
    rule.condition.core.ordinaryIterationScope =
      .ok rule.iterationScope :=
  rule.iterationScopeOwned

/-- A mixed rule with no per-row reference scope and a repeatable error declaration has the distinct once plan; it cannot silently become scalar or validation-row iteration. -/
theorem checkedValidationRule_once_plan_exact
    (rule : CheckedResolvedValidationRule model)
    (noScope : rule.iterationScope = none)
    (repeatable :
      rule.errorPlacement.repeatableScope.isEmpty = false) :
    rule.ordinaryIterationPlan =
      .once rule.errorPlacement.repeatableScope := by
  simp [CheckedResolvedValidationRule.ordinaryIterationPlan,
    CheckedResolvedValidationRule.iteratedScope, noScope, repeatable]

/-- The rule gates allowed to refuse an unguarded negative iteration before its own class: the
measured ones, and a group target's refusals that carry no class. -/
def FlatRuleAssemblyError.precedesNegativeIteration : FlatRuleAssemblyError → Bool
  | .unboundOperandLevel _ _ | .errorFieldIterationInvalid _ _ | .formOnlyIteration _ _
  | .errorFieldNotReferenced _ | .groupErrorTarget _ (.unbound _)
  | .groupErrorTarget _ (.iterationInvalid _) | .groupErrorTarget _ .notReferenced
  | .groupErrorTarget _ .declaringGroup | .groupErrorTarget _ .unknown
  | .groupErrorTarget _ .unsupported => true
  | _ => false

theorem flatRuleAssemblyError_unboundLevel_precedes {model : FlatModel} {ruleGroup : GroupPath}
    {error unbound : FlatRuleAssemblyError}
    (found : error.unboundLevel? model ruleGroup = some unbound) :
    unbound.precedesNegativeIteration = true := by
  unfold FlatRuleAssemblyError.unboundLevel? at found
  split at found <;> (try split at found) <;> (try simp only [Option.map_eq_some_iff] at found) <;>
    first
    | (obtain ⟨_, _, rfl⟩ := found; rfl)
    | cases found

/-- An unguarded repeatable condition is refused, possibly first by the error entity's scope,
reference-binding or reference gate (spec/07 §1). Legality is judged at the levels the rule
iterates, so a level the error field's key selection fixes is left out. -/
theorem assembleResolvedValidationRule_rejects_negativeIteration
    (model : FlatModel) (condition : CheckedValidationCondition model)
    (errorEntity : RuleErrorEntity) (errorCode : String)
    (severity : ValidationSeverity) (messagePlan : MessageRenderPlan)
    (level : RepeatableLevel)
    (invalid :
      condition.core.iterationLegality (errorEntity.selectionBound condition.core) =
        .ok (.invalid level)) :
    ∃ error, assembleResolvedValidationRuleFor model condition errorEntity errorCode
        severity messagePlan = .error error ∧
      (error = .negativeConditionInIteration level ∨ error.precedesNegativeIteration = true) := by
  cases errorEntity <;>
    unfold assembleResolvedValidationRuleFor assembleResolvedValidationRuleFor.finish
      assembleResolvedValidationRuleFor.negativeLevel? <;>
    simp only [RuleErrorEntity.selectionBound] at invalid ⊢ <;> simp only [invalid] <;>
    repeat' split
  all_goals first
    | exact ⟨_, rfl, Or.inl rfl⟩
    | exact ⟨_, rfl, Or.inr rfl⟩
    | exact ⟨_, rfl, Or.inr (flatRuleAssemblyError_unboundLevel_precedes ‹_›)⟩

/-- The already-derived negative-iteration assembly error projects to the exact measured Kernel diagnostic class. -/
theorem flatRuleAssemblyError_negativeIteration_diagnostic
    (level : RepeatableLevel) :
    FlatRuleAssemblyError.diagnostic?
        (.negativeConditionInIteration level) =
      some KernelStaticDiagnostic.negativeConditionInIteration := by
  rfl

/-- The scalar checked entry point reports missing addressed context before evaluating a repeatable condition; it cannot manufacture semantic UNKNOWN. -/
theorem checkedValidationRule_scalar_rejects_addressed
    (rule : CheckedResolvedValidationRule model)
    (prepared : PreparedFlatStringContext model compilePattern)
    (locale : String) (raw : RawFlatContext) (groups : GroupPresenceContext)
    (hasContent : Bool)
    (addressed : rule.requiresAddressedValidation = true) :
    rule.evalFull prepared locale raw groups hasContent =
      .error .addressedContextRequired := by
  simp [CheckedResolvedValidationRule.evalFull, addressed]

/-- The checked whole-rule partial route preserves the observable filtered-rule invariant: a retained `Having` skips without addressed-context demand or condition evaluation. -/
theorem checkedValidationRule_partial_filtered_skips
    (rule : CheckedResolvedValidationRule model)
    (prepared : PreparedFlatStringContext model compilePattern)
    (locale : String) (raw : RawFlatContext)
    (groups : GroupPresenceContext) (scope : ValidationRelevanceScope)
    (field : FieldId) (fieldTarget : rule.errorField? = some field)
    (filtered : rule.hasHaving = true) :
    rule.evalPartial prepared locale raw groups scope =
      .ok .skipped := by
  simp [CheckedResolvedValidationRule.evalPartial,
    FlatRuleFilterPresence.admits, fieldTarget, filtered]

/-- After global augmentation and the iteration-bound error-field gate, an admitted scalar partial rule delegates exactly once to the existing exact-cell relevance-aware condition tree and sole message emitter. -/
theorem checkedValidationRule_partial_evaluated
    (rule : CheckedResolvedValidationRule model)
    (prepared : PreparedFlatStringContext model compilePattern)
    (locale : String) (raw : RawFlatContext)
    (groups : GroupPresenceContext) (scope : ValidationRelevanceScope)
    (unfiltered : rule.hasHaving = false)
    (field : FieldId) (fieldTarget : rule.errorField? = some field)
    (errorRelevant :
      (scope.withGlobals model).coversFieldAtBoundLevels model
        field rule.partialErrorBoundLevels [] = true)
    (scalar : rule.requiresAddressedValidation = false) :
    rule.evalPartial prepared locale raw groups scope =
      .ok (.evaluated (rule.core.emitEvaluationResult
        (rule.condition.core.evalSelectedResult {
          fields := (prepared.checkContext locale raw).withWorld prepared.world
          groups
          pass := .part
        } fun field =>
          (scope.withGlobals model).coversField model field []))) := by
  simp [CheckedResolvedValidationRule.evalPartial,
    FlatRuleFilterPresence.admits, unfiltered, fieldTarget, errorRelevant, scalar]

/-- A filtered repeatable rule skips before support checks, iteration-scope demand, or document-row construction. -/
theorem checkedValidationRule_partial_repeatable_filtered_skips
    (rule : CheckedResolvedValidationRule model)
    (checked : CheckedDocument model)
    (scope : ValidationRelevanceScope)
    (field : FieldId) (fieldTarget : rule.errorField? = some field)
    (filtered : rule.hasHaving = true) :
    rule.evalOrdinaryRepeatablePartial checked scope =
      .ok .skipped := by
  simp [CheckedResolvedValidationRule.evalOrdinaryRepeatablePartial,
    CheckedResolvedValidationRule.skipsPartialCall, fieldTarget, filtered] <;> rfl

/-- Once the call-local preliminary view is built, the unfiltered convenience boundary delegates to its prepared evaluator without rebuilding relevance inside the rule. -/
theorem checkedValidationRule_partial_repeatable_prepared
    (rule : CheckedResolvedValidationRule model)
    (checked : CheckedDocument model)
    (scope : ValidationRelevanceScope)
    (preliminary : CheckedPartialPreliminary model)
    (field : FieldId) (fieldTarget : rule.errorField? = some field)
    (unfiltered : rule.hasHaving = false)
    (prepared :
      checked.applyPartialGeneratedPreliminaryForScope scope =
        .ok preliminary) :
    rule.evalOrdinaryRepeatablePartial checked scope =
      rule.evalOrdinaryRepeatablePartialPrepared preliminary := by
  simp [CheckedResolvedValidationRule.evalOrdinaryRepeatablePartial,
    CheckedResolvedValidationRule.skipsPartialCall, fieldTarget, unfiltered, prepared] <;> rfl

/-- At the prepared one-row boundary, error-path nonrelevance at the iteration-bound levels is a rule skip rather than semantic UNKNOWN and prevents every addressed read. -/
theorem checkedValidationRule_partial_repeatable_irrelevant_row_skips
    (rule : CheckedResolvedValidationRule model)
    (preliminary : CheckedPartialPreliminary model)
    (environment : Env)
    (supported : rule.supportsOrdinaryRepeatablePartial = true)
    (field : FieldId) (fieldTarget : rule.errorField? = some field)
    (irrelevant :
      preliminary.relevance.coversFieldAtBoundLevels model field
        rule.partialErrorBoundLevels environment = false) :
    rule.evalOrdinaryRepeatablePartialAtPrepared preliminary environment =
      .ok (environment, .skipped) := by
  simp [CheckedResolvedValidationRule.evalOrdinaryRepeatablePartialAtPrepared,
    supported, fieldTarget, irrelevant] <;> rfl

/-- A filtered once rule skips before support, plan construction, relevance, or document reads. -/
theorem checkedValidationRule_partial_once_filtered_skips
    (rule : CheckedResolvedValidationRule model)
    (checked : CheckedDocument model)
    (scope : ValidationRelevanceScope)
    (field : FieldId) (fieldTarget : rule.errorField? = some field)
    (filtered : rule.hasHaving = true) :
  rule.evalOrdinaryOncePartial checked scope =
      .ok .skipped := by
  simp [CheckedResolvedValidationRule.evalOrdinaryOncePartial,
    CheckedResolvedValidationRule.skipsPartialCall, fieldTarget, filtered] <;> rfl

/-- A once plan binds no error-field repetition level even though its message pointer retains the all-one error environment. -/
theorem checkedValidationRule_partialErrorBoundLevels_once
    (rule : CheckedResolvedValidationRule model)
    (errorScope : List RepeatableLevel)
    (once : rule.ordinaryIterationPlan = .once errorScope) :
    rule.partialErrorBoundLevels = [] := by
  simp [CheckedResolvedValidationRule.partialErrorBoundLevels, once]

/-- After a supported once environment is constructed, an error path absent from the whole relevant set skips before condition or target reads. Concrete coordinates below the empty bound remain intentionally ignored. -/
theorem checkedValidationRule_partial_once_irrelevant_skips
    (rule : CheckedResolvedValidationRule model)
    (preliminary : CheckedPartialPreliminary model)
    (errorScope : List RepeatableLevel)
    (unfiltered : rule.hasHaving = false)
    (supported : rule.supportsOrdinaryRepeatablePartial = true)
    (once : rule.ordinaryIterationPlan = .once errorScope)
    (field : FieldId) (fieldTarget : rule.errorField? = some field)
    (irrelevant :
      preliminary.relevance.coversFieldAtBoundLevels model field []
          (errorScope.map fun level => (level, 1)) = false) :
    rule.evalOrdinaryOncePartialPrepared preliminary =
      .ok .skipped := by
  simp [CheckedResolvedValidationRule.evalOrdinaryOncePartialPrepared,
    CheckedResolvedValidationRule.onceEnvironment,
    CheckedResolvedValidationRule.partialErrorBoundLevels,
    CheckedResolvedValidationRule.skipsPartialCall,
    unfiltered, supported, once, fieldTarget, irrelevant] <;> rfl

/-- Checked assembly preserves its explicit error field and metadata through message emission. -/
theorem checkedFlatRule_fired_message_exact
    (rule : CheckedResolvedFlatRule model)
    (prepared : PreparedFlatStringContext model compilePattern)
    (locale : String) (raw : RawFlatContext) (hasContent : Bool)
    (messageType : Polarity)
    (fires :
      rule.condition.core.evalFull
        ((prepared.checkContext locale raw).withWorld prepared.world) hasContent =
        .fired messageType) :
    rule.evalFull prepared locale raw hasContent =
      .fired {
        errorAddress := { entity := rule.errorEntity, coordinates := [] }
        errorCode := rule.errorCode
        severity := rule.severity
        messageType
        text := rule.messagePlan.render
      } := by
  simpa only [CheckedResolvedFlatRule.evalFull,
    CheckedResolvedFlatRule.core] using
    flatRule_fired_message_exact rule.core
      ((prepared.checkContext locale raw).withWorld prepared.world)
      hasContent messageType fires

/-- Checked mixed assembly preserves exact metadata and the evaluation origin needed by message-reference selection. -/
theorem checkedValidationRule_fired_message_exact
    (rule : CheckedResolvedValidationRule model)
    (prepared : PreparedFlatStringContext model compilePattern)
    (locale : String) (raw : RawFlatContext) (groups : GroupPresenceContext)
    (hasContent : Bool) (messageType : Polarity)
    (scalar : rule.requiresAddressedValidation = false)
    (fires :
      rule.condition.core.evalFull {
        fields := (prepared.checkContext locale raw).withWorld prepared.world
        groups
      } hasContent =
        .fired messageType) :
    rule.evalFull prepared locale raw groups hasContent =
      .ok (.fired {
        errorAddress := { entity := rule.errorEntity, coordinates := [] }
        errorCode := rule.errorCode
        severity := rule.severity
        messageType
        text := rule.messagePlan.render
        origin := match rule.condition.core.evalSelectedResult {
          fields := (prepared.checkContext locale raw).withWorld prepared.world
          groups
        } with
          | .ok _ => .condition
          | .error _ => .runtimeFailure
      }) := by
  unfold ValidationCondition.evalFull at fires
  split at fires
  · rename_i content
    cases h : rule.condition.core.evalSelectedResult {
        fields := (prepared.checkContext locale raw).withWorld prepared.world
        groups } with
    | ok verdict =>
        simp [ValidationCondition.evalSelected, h, Except.toOption] at fires
        simp [CheckedResolvedValidationRule.evalFull, ResolvedValidationRule.evalFull,
          CheckedResolvedValidationRule.core, ResolvedValidationRule.emitEvaluationResult,
          ResolvedRule.emit, ResolvedRule.emitAt, ResolvedRule.emitAtCoordinates,
          scalar, h, fires, content]
    | error fault =>
        simp [ValidationCondition.evalSelected, h, Except.toOption] at fires
        simp [CheckedResolvedValidationRule.evalFull, ResolvedValidationRule.evalFull,
          CheckedResolvedValidationRule.core, ResolvedValidationRule.emitEvaluationResult,
          ResolvedRule.emitRuntimeFailureAt, ResolvedRule.emitAt,
          ResolvedRule.emitAtCoordinates, scalar, h, ← fires, content]
  · contradiction

end A12Kernel
