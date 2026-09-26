import A12Kernel.Elaboration.StringPatternMessage
import A12Kernel.Proofs.ValidationMessageAuthoring

/-! # en_US String-pattern message producer laws

The producer lowers caller-selected bytes without reinterpreting them and decorates an
already-established formal error without replacing it. -/

namespace A12Kernel

theorem checkedEnUsStringPatternMessage_fieldValue_isOpaque
    (inputs : StringPatternMessageInputs) :
    (CheckedEnUsStringPatternMessagePart.fieldValue
      |>.toRenderPart inputs
      |>.render) = inputs.fieldValue := by
  rfl

/-- The field's pattern message shares the rule message's repertoire composition, so a source whose
repertoire check fails is never admitted either. -/
theorem enUsStringPatternMessageTemplate_repertoireFailure_refused
    (source : String) (character : Char)
    (failure : firstUnsupportedMessageTemplateCharacter? source = some character) :
    (elaborateEnUsStringPatternMessageTemplate source).isOk = false :=
  withMessageRepertoire_repertoireFailure_refused _ _ _ failure

theorem checkedEnUsStringPatternMessage_rendering_preservesPatternError
    (template : CheckedEnUsStringPatternMessageTemplate)
    (inputs : StringPatternMessageInputs) :
    (template.renderError inputs).error = .pattern := by
  rfl

end A12Kernel
