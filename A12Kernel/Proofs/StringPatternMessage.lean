import A12Kernel.Elaboration.StringPatternMessage
import A12Kernel.Proofs.ValidationMessageAuthoring

/-! # String-pattern message producer laws

The producer lowers caller-selected bytes without reinterpreting them and decorates an
already-established formal error without replacing it. -/

namespace A12Kernel

theorem checkedStringPatternMessage_fieldValue_isOpaque
    (inputs : StringPatternMessageInputs) :
    (CheckedStringPatternMessagePart.fieldValue
      |>.toRenderPart inputs
      |>.render) = inputs.fieldValue := by
  rfl

/-- The field's pattern message shares the rule message's repertoire composition, so a source whose
repertoire check fails is never admitted either. -/
theorem stringPatternMessageTemplate_repertoireFailure_refused
    (tokens : StringPatternMessageTokens) (source : String) (character : Char)
    (failure : firstUnsupportedMessageTemplateCharacter? source = some character) :
    (elaborateStringPatternMessageTemplate tokens source).isOk = false :=
  withMessageRepertoire_repertoireFailure_refused _ _ _ failure

theorem checkedStringPatternMessage_rendering_preservesPatternError
    (template : CheckedStringPatternMessageTemplate)
    (inputs : StringPatternMessageInputs) :
    (template.renderError inputs).error = .pattern := by
  rfl

end A12Kernel
