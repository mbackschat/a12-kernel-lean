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

end A12Kernel
