import A12Kernel.Elaboration.ValidationMessageAuthoring
import A12Kernel.Proofs.ValidationRule

/-! # Laws for checked validation-message authoring -/

namespace A12Kernel

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

/-- The group position's gate is genuinely applied at its entry point: every admitted absolute
argument contains the rule's group, so nothing below the rule is ever reached through it. -/
theorem checkMessageGroup_absolute_containsRuleGroup
    {model : FlatModel} {condition : CheckedFlatCondition model}
    {parameter : String} {path : GroupPath}
    {access : CheckedValidationMessageGroup model condition}
    (admitted : checkMessageGroup condition parameter (.absolute path) = .ok access) :
    GroupPath.isPrefixOf path condition.rowGroup = true := by
  rw [checkMessageGroup] at admitted
  split at admitted
  · split at admitted
    · assumption
    · cases admitted
  · cases admitted

/-- Both keyword shorthands are admitted whenever the rule's group is a representable path, and each
resolves to one endpoint of that group's own ancestor chain. They are therefore shorthands inside the
one containment gate rather than admissions beside it. -/
theorem checkMessageGroup_ruleGroup_resolvesToRuleGroup
    {model : FlatModel} {condition : CheckedFlatCondition model}
    (parameter : String)
    (valid : GroupPath.isValid condition.rowGroup = true) :
    (checkMessageGroup condition parameter .ruleGroup).map
        (fun access => access.group) = .ok condition.rowGroup := by
  rw [checkMessageGroup]
  simp only [valid, groupPath_isPrefixOf_self, dite_true]
  rfl

theorem checkMessageGroup_rootGroup_resolvesToChainRoot
    {model : FlatModel} {condition : CheckedFlatCondition model}
    (parameter : String)
    (valid : GroupPath.isValid condition.rowGroup = true) :
    (checkMessageGroup condition parameter .rootGroup).map
        (fun access => access.group) = .ok (condition.rowGroup.take 1) := by
  rw [checkMessageGroup]
  simp only [groupPath_isValid_take_one valid, groupPath_take_isPrefixOf,
    dite_true]
  rfl

end A12Kernel
