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

/-- The addressed emitter preserves the exact verdict while changing only metadata on a firing. -/
@[simp]
theorem resolvedRule_emitAt_verdict (rule : ResolvedRule Condition)
    (errorPath : List Nat) (verdict : Verdict) :
    (rule.emitAt errorPath verdict).verdict = verdict := by
  cases verdict <;> rfl

/-- A firing carries the caller-resolved path through the sole emitter unchanged. -/
@[simp]
theorem resolvedRule_emitAt_fired_exact (rule : ResolvedRule Condition)
    (errorPath : List Nat) (messageType : Polarity) :
    rule.emitAt errorPath (.fired messageType) =
      .fired {
        errorAddress := { field := rule.errorField, path := errorPath }
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
  exact resolvedRule_evalWith_verdict rule
    (fun condition => condition.evalFull context hasContent)

/-- A fired condition copies the exact resolved address and supplied metadata, renders the structured plan, and derives its message type from the verdict. -/
theorem flatRule_fired_message_exact (rule : ResolvedFlatRule)
    (context : FlatContext) (hasContent : Bool) (messageType : Polarity)
    (fires : rule.condition.evalFull context hasContent = .fired messageType) :
    rule.evalFull context hasContent =
      .fired {
        errorAddress := { field := rule.errorField, path := [] }
        errorCode := rule.errorCode
        severity := rule.severity
        messageType
        text := rule.messagePlan.render
  } := by
  simp [ResolvedRule.evalFull, ResolvedRule.evalWith,
    ResolvedRule.evalWithAt, ResolvedRule.emitAt, fires]

/-- Error address, code, severity, and already-resolved text cannot change firing or polarity. -/
theorem flatRule_metadata_doesNotChangeVerdict (rule : ResolvedFlatRule)
    (errorField : FieldId) (errorCode : String)
    (severity : ValidationSeverity)
    (messagePlan : MessageRenderPlan)
    (context : FlatContext) (hasContent : Bool) :
    (({ rule with errorField, errorCode, severity, messagePlan }).evalFull
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
    ResolvedRule.evalWithAt, ResolvedRule.emitAt, notFired]

/-- An unavailable condition likewise suppresses message resolution rather than manufacturing text. -/
theorem flatRule_unknown_independentOfMessagePlan
    (rule : ResolvedFlatRule) (otherPlan : MessageRenderPlan)
    (context : FlatContext) (hasContent : Bool)
    (unknown : rule.condition.evalFull context hasContent = .unknown) :
    ({ rule with messagePlan := otherPlan }).evalFull context hasContent =
      rule.evalFull context hasContent := by
  simp [ResolvedRule.evalFull, ResolvedRule.evalWith,
    ResolvedRule.evalWithAt, ResolvedRule.emitAt, unknown]

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

/-- Flat checked assembly carries one unique, nonrepeatable, referenced error declaration from the same model as the condition. -/
theorem checkedFlatRule_errorField_coherent
    (rule : CheckedResolvedFlatRule model) :
    model.lookupUniqueId rule.errorField = .ok rule.errorDeclaration ∧
      rule.errorDeclaration.repeatableScope.isEmpty = true ∧
      rule.condition.core.referencesField rule.errorField = true :=
  by
    have noScope : rule.iterationScope = none := by
      simpa using rule.iterationScopeOwned.symm
    exact ⟨rule.errorFieldLookup,
      by
        simpa [ruleErrorScopeCompatible, noScope] using
          rule.errorFieldScopeCompatible,
      rule.errorFieldReferenced⟩

/-- Mixed checked assembly uses the shared traversal to certify the exact error declaration and its derived ordinary iteration scope. -/
theorem checkedValidationRule_errorField_coherent
    (rule : CheckedResolvedValidationRule model) :
    model.lookupUniqueId rule.errorField = .ok rule.errorDeclaration ∧
      ruleErrorScopeCompatible rule.errorDeclaration rule.iterationScope = true ∧
      rule.condition.core.referencesField rule.errorField = true :=
  ⟨rule.errorFieldLookup, rule.errorFieldScopeCompatible,
    rule.errorFieldReferenced⟩

/-- Checked assembly cannot substitute a caller-selected ordinary iteration scope for the one derived from the complete checked condition tree. -/
theorem checkedValidationRule_iterationScope_owned
    (rule : CheckedResolvedValidationRule model) :
    rule.condition.core.ordinaryIterationScope =
      .ok rule.iterationScope :=
  rule.iterationScopeOwned

/-- Checked rule assembly rejects the first known unguarded repeatable level before it can enter runtime evaluation. -/
theorem assembleResolvedValidationRule_rejects_negativeIteration
    (model : FlatModel) (condition : CheckedValidationCondition model)
    (errorField : FieldId) (errorCode : String)
    (severity : ValidationSeverity) (messagePlan : MessageRenderPlan)
    (level : RepeatableLevel)
    (invalid :
      condition.core.iterationLegality = .ok (.invalid level)) :
    assembleResolvedValidationRule model condition errorField errorCode
        severity messagePlan =
      .error (.negativeConditionInIteration level) := by
  simp [assembleResolvedValidationRule, invalid]

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
        errorAddress := { field := rule.errorField, path := [] }
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

/-- Checked mixed assembly preserves the same exact fired-message contract. -/
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
        errorAddress := { field := rule.errorField, path := [] }
        errorCode := rule.errorCode
        severity := rule.severity
        messageType
        text := rule.messagePlan.render
      }) := by
  simp [CheckedResolvedValidationRule.evalFull,
    CheckedResolvedValidationRule.core, ResolvedValidationRule.evalFull,
    ResolvedRule.evalWith, ResolvedRule.evalWithAt, ResolvedRule.emitAt,
    scalar, fires]

end A12Kernel
