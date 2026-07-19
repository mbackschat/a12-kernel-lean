import A12Kernel.Elaboration.ValidationRule

/-! # Whole-rule and checked-assembly laws -/

namespace A12Kernel

/-- Forgetting emitted metadata recovers exactly the verdict of the reused condition evaluator. -/
theorem flatRule_eval_verdict (rule : ResolvedFlatRule)
    (context : FlatContext) (hasContent : Bool) :
    (rule.evalFull context hasContent).verdict =
      rule.condition.evalFull context hasContent := by
  unfold ResolvedFlatRule.evalFull
  generalize verdictEq :
    rule.condition.evalFull context hasContent = verdict
  cases verdict <;> simp only [FlatRuleOutcome.verdict]

/-- A fired condition copies the exact resolved address and supplied metadata while deriving its message type from the verdict. -/
theorem flatRule_fired_message_exact (rule : ResolvedFlatRule)
    (context : FlatContext) (hasContent : Bool) (messageType : Polarity)
    (fires : rule.condition.evalFull context hasContent = .fired messageType) :
    rule.evalFull context hasContent =
      .fired {
        errorAddress := { field := rule.errorField, path := [] }
        severity := rule.severity
        messageType
        text := rule.resolvedText
      } := by
  simp only [ResolvedFlatRule.evalFull, fires]

/-- Error address, severity, and already-resolved text cannot change firing or polarity. -/
theorem flatRule_metadata_doesNotChangeVerdict (rule : ResolvedFlatRule)
    (errorField : FieldId) (severity : ValidationSeverity)
    (resolvedText : ResolvedMessageText)
    (context : FlatContext) (hasContent : Bool) :
    (({ rule with errorField, severity, resolvedText }).evalFull
        context hasContent).verdict =
      (rule.evalFull context hasContent).verdict := by
  rw [flatRule_eval_verdict, flatRule_eval_verdict]

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

/-- Checked assembly carries one unique, nonrepeatable, referenced error declaration from the same model as the condition. -/
theorem checkedFlatRule_errorField_coherent
    (rule : CheckedResolvedFlatRule model) :
    model.lookupUniqueId rule.errorField = .ok rule.errorDeclaration ∧
      rule.errorDeclaration.repeatableScope.isEmpty = true ∧
      rule.condition.core.referencesField rule.errorField = true :=
  ⟨rule.errorFieldLookup, rule.errorFieldNonrepeatable,
    rule.errorFieldReferenced⟩

/-- Checked assembly preserves its explicit error field and metadata through message emission. -/
theorem checkedFlatRule_fired_message_exact
    (rule : CheckedResolvedFlatRule model) (raw : RawFlatContext)
    (hasContent : Bool) (messageType : Polarity)
    (fires :
      rule.condition.core.evalFull (model.checkContext raw) hasContent =
        .fired messageType) :
    rule.evalFull raw hasContent =
      .fired {
        errorAddress := { field := rule.errorField, path := [] }
        severity := rule.severity
        messageType
        text := rule.resolvedText
      } := by
  simpa only [CheckedResolvedFlatRule.evalFull,
    CheckedResolvedFlatRule.core] using
    flatRule_fired_message_exact rule.core (model.checkContext raw)
      hasContent messageType fires

end A12Kernel
