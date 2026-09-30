import A12Kernel.Elaboration.ValidationMessageAuthoring
import A12Kernel.Proofs.ValidationRule

/-! # Laws for checked validation-message authoring -/

namespace A12Kernel

/-- A source whose repertoire check fails is refused with the first unsupported character, and the
producer's own first failure, when it has one, stands beside it rather than being dropped or
replaced: the co-reporting both message producers share. -/
theorem withMessageRepertoire_repertoireFailure {α : Type}
    (source : String) (checked : Except ValidationMessageTemplateError α) (character : Char)
    (failure : firstUnsupportedMessageTemplateCharacter? source = some character) :
    withMessageRepertoire source checked =
      .error (match checked with
        | .ok _ => .unsupportedCharacter character
        | .error cause => .unsupportedCharacterWithError character cause) := by
  unfold withMessageRepertoire
  rw [failure]
  cases checked <;> rfl

/-- A source whose repertoire check passes keeps the producer's own result unchanged. -/
theorem withMessageRepertoire_repertoirePass {α : Type}
    (source : String) (checked : Except ValidationMessageTemplateError α)
    (pass : firstUnsupportedMessageTemplateCharacter? source = none) :
    withMessageRepertoire source checked = checked := by
  unfold withMessageRepertoire
  rw [pass]

/-- The repertoire composition never admits a source whose repertoire check fails, whatever the
producer's own result was. -/
theorem withMessageRepertoire_repertoireFailure_refused {α : Type}
    (source : String) (checked : Except ValidationMessageTemplateError α) (character : Char)
    (failure : firstUnsupportedMessageTemplateCharacter? source = some character) :
    (withMessageRepertoire source checked).isOk = false := by
  rw [withMessageRepertoire_repertoireFailure source checked character failure]
  rfl

/-- Co-reporting never admits a template whose repertoire check fails, even when every parameter checks. -/
theorem validationMessageTemplate_repertoireFailure_refused
    (model : FlatModel) (profile : ValidationMessageKeywordProfile)
    (condition : CheckedFlatCondition model) (source : String) (character : Char)
    (failure : firstUnsupportedMessageTemplateCharacter? source = some character) :
    (elaborateValidationMessageTemplate model profile condition source).isOk = false :=
  withMessageRepertoire_repertoireFailure_refused _ _ _ failure

theorem checkedValidationMessageReference_usedByCondition
    (reference : CheckedValidationMessageReference model condition) :
    condition.core.referencesField reference.declaration.id = true :=
  reference.conditionReferenced

theorem checkedValidationMessage_fieldValue_present_isOpaque
    (reference : CheckedValidationMessageReference model condition)
    (inputs : ValidationMessageInputs) (value defaultDisplay : String)
    (selected :
      inputs.fieldValue reference.declaration.id = {
        displayValue := some value
        defaultDisplay
      })
    (nonempty : value.isEmpty = false) :
    (CheckedValidationMessagePart.fieldValue reference
      |>.toRenderPart inputs
      |>.render) = value := by
  simp [CheckedValidationMessagePart.toRenderPart, selected,
    MessageRenderPart.render, MessageValueInput.resolve, nonempty]

theorem checkedValidationMessage_inputs_doNotChangeVerdict
    (rule : ResolvedFlatRule)
    (template : CheckedValidationMessageTemplate model condition)
    (left right : ValidationMessageInputs)
    (context : FlatContext) (hasContent : Bool) :
    (({ rule with messagePlan := template.toRenderPlan left }).evalFull
        context hasContent).verdict =
      (({ rule with messagePlan := template.toRenderPlan right }).evalFull
        context hasContent).verdict := by
  rw [flatRule_eval_verdict, flatRule_eval_verdict]

private theorem groupPath_isPrefixOf_self (path : GroupPath) :
    GroupPath.isPrefixOf path path = true := by
  induction path with
  | nil => rfl
  | cons _ _ ih => simp [GroupPath.isPrefixOf, ih]

private theorem groupPath_take_isPrefixOf (path : GroupPath) (count : Nat) :
    GroupPath.isPrefixOf (path.take count) path = true := by
  induction path generalizing count with
  | nil => cases count <;> rfl
  | cons _ tail ih =>
      cases count with
      | zero => rfl
      | succ n => simp [GroupPath.isPrefixOf, ih n]

private theorem groupPath_isValid_take_one {path : GroupPath}
    (valid : GroupPath.isValid path = true) :
    GroupPath.isValid (path.take 1) = true := by
  cases path with
  | nil => exact valid
  | cons _ _ =>
      simp [GroupPath.isValid] at valid ⊢
      exact valid.1

/-- The group position's gates are genuinely applied at its entry point: every admitted absolute
argument names a declared root group **and** is available to the rule's message, so nothing under an
undeclared root, and no group the rule neither lies in nor reads into, is ever reached through it. -/
theorem checkMessageGroup_absolute_admitted
    {model : FlatModel} {condition : CheckedFlatCondition model}
    {parameter : String} {path : GroupPath}
    {access : CheckedValidationMessageGroup model condition}
    (admitted : checkMessageGroup condition parameter (.absolute path) = .ok access) :
    messageGroupAvailable model condition path = true ∧
      model.hasGroupPath (path.take 1) = true := by
  cases path with
  | nil => cases admitted
  | cons root rest =>
      rw [checkMessageGroup] at admitted
      split at admitted
      case isFalse => cases admitted
      case isTrue hRoot =>
        rw [admitMessageGroup] at admitted
        split at admitted
        · split at admitted
          · exact ⟨by assumption, hRoot⟩
          · cases admitted
        · cases admitted

/-- The rule-group shorthand resolves to the rule's own group — **once its placement admits it**. The
extra hypothesis is the whole difference between the two shorthands: `RootGroup` needs only a
representable path, while `RuleGroup` additionally needs the rule to sit below the root, so the two are
not one gate with two spellings. Without the hypothesis this statement was provable and wrong, which is
what the placement gate corrected. -/
theorem checkMessageGroup_ruleGroup_resolvesToRuleGroup
    {model : FlatModel} {condition : CheckedFlatCondition model}
    (parameter : String)
    (valid : GroupPath.isValid condition.rowGroup = true)
    (belowRoot : ¬ condition.rowGroup.length ≤ 1) :
    (checkMessageGroup condition parameter .ruleGroup).map
        (fun access => access.group) = .ok condition.rowGroup := by
  rw [checkMessageGroup]
  simp only [belowRoot, if_false, admitMessageGroup, valid,
    messageGroupAvailable, groupPath_isPrefixOf_self, Bool.true_or, dite_true]
  rfl

/-- The negative direction, and the one a consumer actually needs: at a root locus the shorthand is
refused whatever else is well formed. The admission law above is satisfied by an implementation that
dropped the gate entirely, so it cannot carry this on its own. -/
theorem checkMessageGroup_ruleGroup_refusedAtRootLocus
    {model : FlatModel} {condition : CheckedFlatCondition model}
    (parameter : String)
    (atRoot : condition.rowGroup.length ≤ 1) :
    checkMessageGroup condition parameter .ruleGroup =
      .error (.ruleGroupImmediatelyBelowRoot parameter) := by
  rw [checkMessageGroup]
  simp only [atRoot, if_true]

theorem checkMessageGroup_rootGroup_resolvesToChainRoot
    {model : FlatModel} {condition : CheckedFlatCondition model}
    (parameter : String)
    (valid : GroupPath.isValid condition.rowGroup = true) :
    (checkMessageGroup condition parameter .rootGroup).map
        (fun access => access.group) = .ok (condition.rowGroup.take 1) := by
  rw [checkMessageGroup, admitMessageGroup]
  simp only [groupPath_isValid_take_one valid, messageGroupAvailable, groupPath_take_isPrefixOf,
    Bool.true_or,
    dite_true]
  rfl

end A12Kernel
