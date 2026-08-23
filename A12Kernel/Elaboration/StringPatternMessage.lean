import A12Kernel.Elaboration.ValidationMessageAuthoring

/-! # The measured en_US String-pattern field-message producer

A String field's own pattern message is a **different producer** from a rule's error text, sharing
only the lexical gate and the refusal type. Its parameter vocabulary is two fixed lowercase tokens
naming the owning field, never a rule-relative path, so it performs no lookup and needs no model,
condition, or keyword profile. Its empty dollar pair is an invalid parameter rather than the rule
path's literal-dollar escape.

Rendering lowers caller-selected bytes directly as opaque text: this producer applies neither the rule
path's provider/label cascade nor its empty-display default, and it never reclassifies the established
formal `pattern` error it decorates. -/

namespace A12Kernel

/-- One checked part of the measured en_US String-pattern field-message grammar. The fixed tokens refer to the owning field, never to a rule-relative path. -/
inductive CheckedEnUsStringPatternMessagePart where
  | text (value : String)
  | fieldName
  | fieldValue
  deriving Repr, DecidableEq

/-- A checked en_US String-pattern error-text template. Requiredness and every other field-message producer remain distinct and unsupported. -/
structure CheckedEnUsStringPatternMessageTemplate where
  source : String
  parts : List CheckedEnUsStringPatternMessagePart
  deriving Repr, DecidableEq

private def stringPatternTextPart (value : String) :
    List CheckedEnUsStringPatternMessagePart :=
  if value.isEmpty then [] else [.text value]

private def parseEnUsStringPatternParameter (parameter : String) :
    Except ValidationMessageTemplateError CheckedEnUsStringPatternMessagePart :=
  match parameter with
  | "field" => .ok .fieldName
  | "field.value" => .ok .fieldValue
  | _ => .error (.invalidParameter parameter)

private def parseEnUsStringPatternSegments :
    List String →
      Except ValidationMessageTemplateError
        (List CheckedEnUsStringPatternMessagePart)
  | [] => .ok []
  | [text] => .ok (stringPatternTextPart text)
  | text :: parameter :: rest => do
      let parameterPart ← parseEnUsStringPatternParameter parameter
      pure (stringPatternTextPart text ++ [parameterPart] ++
        (← parseEnUsStringPatternSegments rest))

/-- Check the bounded English String-pattern producer. Its empty dollar-pair parameter is invalid rather than a literal-dollar escape. -/
def elaborateEnUsStringPatternMessageTemplate (source : String) :
    Except ValidationMessageTemplateError
      CheckedEnUsStringPatternMessageTemplate := do
  let segments ← validateMessageTemplateSource source
  pure { source, parts := ← parseEnUsStringPatternSegments segments }

/-- Exact replacement bytes selected by the caller for the owning field. Provider invocation and empty-value fallback precede this boundary and remain outside the supported fragment. -/
structure StringPatternMessageInputs where
  fieldName : String
  fieldValue : String
  deriving Repr, DecidableEq

def CheckedEnUsStringPatternMessagePart.toRenderPart
    (inputs : StringPatternMessageInputs) :
    CheckedEnUsStringPatternMessagePart → MessageRenderPart
  | .text value => .text value
  | .fieldName => .text inputs.fieldName
  | .fieldValue => .text inputs.fieldValue

def CheckedEnUsStringPatternMessageTemplate.toRenderPlan
    (template : CheckedEnUsStringPatternMessageTemplate)
    (inputs : StringPatternMessageInputs) : MessageRenderPlan :=
  { parts := template.parts.map (·.toRenderPart inputs) }

/-- The resolved text attached to an already-established String-pattern failure. Rendering cannot replace or reclassify the underlying formal error. -/
structure RenderedStringPatternError where
  error : StringFieldError
  text : ResolvedMessageText
  deriving Repr, DecidableEq

def CheckedEnUsStringPatternMessageTemplate.renderError
    (template : CheckedEnUsStringPatternMessageTemplate)
    (inputs : StringPatternMessageInputs) : RenderedStringPatternError where
  error := .pattern
  text := (template.toRenderPlan inputs).render

end A12Kernel
