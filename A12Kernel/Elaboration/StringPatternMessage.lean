import A12Kernel.Elaboration.ValidationMessageAuthoring

/-! # The measured String-pattern field-message producer

A String field's own pattern message is a **different producer** from a rule's error text, sharing
the character gates, dollar parity, the repertoire composition and the refusal type. Its parameter
vocabulary is two fixed tokens naming the owning field, never a rule-relative path, so it performs no
lookup and needs no model or condition. The tokens are spelled in the model's **condition language**,
`field` and `field.value` in English and `Feld` and `Feld.Wert` in German, whatever locale the message
is written for ([inbound](../../docs/sources/inbound-handbacks.md#inbound-2026-09-26n-field-message-gates)).

**An empty dollar pair names no parameter and is skipped wherever it stands**: at the start, inside the
text, at the end or alone ([inbound](../../docs/sources/inbound-handbacks.md#inbound-2026-09-26n-field-message-gates);
kernel 31.1.1, a12-dmkits `FieldTypeMessageTextLawsTest` at `1124b523f`, where kernel 30.8.1 refused every one
but a trailing pair as an invalid parameter). That is not the rule path's literal-dollar escape, and a
skipped pair keeps its dollars as literal text: the trailing pair renders verbatim on both runtime strategies
(`Cost $$` renders `Cost $$`, [inbound](../../docs/sources/inbound-handbacks.md#inbound-2026-09-27a-field-message-render)),
and a pair inside the text is given the same account, which no row measures.

Rendering lowers caller-selected bytes directly as opaque text: this producer applies neither the rule
path's provider/label cascade nor its empty-display default, and it never reclassifies the established
formal `pattern` error it decorates. -/

namespace A12Kernel

/-- The two parameter tokens of a field's own message in the model's condition language. The caller
supplies them, as it supplies a rule message's keyword profile, since this project chooses no
language for the author. -/
structure StringPatternMessageTokens where
  field : String
  fieldValue : String
  deriving Repr, DecidableEq

/-- One checked part of the measured String-pattern field-message grammar. The fixed tokens refer to the owning field, never to a rule-relative path. -/
inductive CheckedStringPatternMessagePart where
  | text (value : String)
  | fieldName
  | fieldValue
  deriving Repr, DecidableEq

/-- A checked String-pattern error-text template. Requiredness and every other field-message producer remain distinct and unsupported. -/
structure CheckedStringPatternMessageTemplate where
  source : String
  parts : List CheckedStringPatternMessagePart
  deriving Repr, DecidableEq

private def stringPatternTextPart (value : String) :
    List CheckedStringPatternMessagePart :=
  if value.isEmpty then [] else [.text value]

/-- One parameter piece: an empty pair is skipped, keeping its dollars as text, and any other piece is one of
the two tokens or an invalid parameter. -/
private def parseStringPatternParameter (tokens : StringPatternMessageTokens) (parameter : String) :
    Except ValidationMessageTemplateError CheckedStringPatternMessagePart :=
  if parameter.isEmpty then .ok (.text "$$")
  else if parameter == tokens.field then .ok .fieldName
  else if parameter == tokens.fieldValue then .ok .fieldValue
  else .error (.invalidParameter parameter)

private def parseStringPatternSegments (tokens : StringPatternMessageTokens) :
    List String →
      Except ValidationMessageTemplateError
        (List CheckedStringPatternMessagePart)
  | [] => .ok []
  | [text] => .ok (stringPatternTextPart text)
  | text :: parameter :: rest => do
      let parameterPart ← parseStringPatternParameter tokens parameter
      pure (stringPatternTextPart text ++ [parameterPart] ++
        (← parseStringPatternSegments tokens rest))

/-- Check a field's pattern message against the tokens of the model's condition language. -/
def elaborateStringPatternMessageTemplate (tokens : StringPatternMessageTokens) (source : String) :
    Except ValidationMessageTemplateError
      CheckedStringPatternMessageTemplate :=
  withMessageRepertoire source do
    pure { source, parts := ← parseStringPatternSegments tokens (← validateMessageTemplateSource source) }

/-- Exact replacement bytes selected by the caller for the owning field. Provider invocation and empty-value fallback precede this boundary and remain outside the supported fragment. -/
structure StringPatternMessageInputs where
  fieldName : String
  fieldValue : String
  deriving Repr, DecidableEq

def CheckedStringPatternMessagePart.toRenderPart
    (inputs : StringPatternMessageInputs) :
    CheckedStringPatternMessagePart → MessageRenderPart
  | .text value => .text value
  | .fieldName => .text inputs.fieldName
  | .fieldValue => .text inputs.fieldValue

def CheckedStringPatternMessageTemplate.toRenderPlan
    (template : CheckedStringPatternMessageTemplate)
    (inputs : StringPatternMessageInputs) : MessageRenderPlan :=
  { parts := template.parts.map (·.toRenderPart inputs) }

/-- The resolved text attached to an already-established String-pattern failure. Rendering cannot replace or reclassify the underlying formal error. -/
structure RenderedStringPatternError where
  error : StringFieldError
  text : ResolvedMessageText
  deriving Repr, DecidableEq

def CheckedStringPatternMessageTemplate.renderError
    (template : CheckedStringPatternMessageTemplate)
    (inputs : StringPatternMessageInputs) : RenderedStringPatternError where
  error := .pattern
  text := (template.toRenderPlan inputs).render

end A12Kernel
