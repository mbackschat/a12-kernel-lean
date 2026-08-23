import A12Kernel.Elaboration.StringPatternMessage

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

theorem checkedEnUsStringPatternMessage_rendering_preservesPatternError
    (template : CheckedEnUsStringPatternMessageTemplate)
    (inputs : StringPatternMessageInputs) :
    (template.renderError inputs).error = .pattern := by
  rfl

end A12Kernel
