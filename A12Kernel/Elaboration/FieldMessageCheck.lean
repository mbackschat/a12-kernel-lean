import A12Kernel.Elaboration.StringPatternMessage
import A12Kernel.Elaboration.ValidationMessageDiagnostic

/-! # Which classes a field's own messages draw

A field declaration can carry its own message per locale: a String pattern's invalid-value text, an
Enumeration's invalid-value text, a required field's text, or a String text with no pattern to pair.
The model check reads them as one field, not one text at a time
([`spec/11`](../../spec/11-messages-and-custom.md),
[inbound](../../docs/sources/inbound-handbacks.md#inbound-2026-09-26n-field-message-gates),
[inbound](../../docs/sources/inbound-handbacks.md#inbound-2026-09-27a-field-message-render)):

- the locales are asked **in the order the model declares them**, whatever order the entries are
  written in, and a locale the model does not declare is never asked;
- of two entries for one locale the **later** is asked;
- the texts meet the pattern message's lexical and parameter gates, and only the **first** failing
  locale reports;
- a required field's own text meets no gate, and a field its own `ONLY` filter deletes is never
  reached;
- a String's pattern and its message require each other, and a message counts only as non-blank
  text for a declared locale: with none, a pattern draws `MVK_ERROR_MESSAGE_AND_PATTERN_INVALID`, and
  with one, a String with no pattern draws `MVK_ERROR_MESSAGE_AND_NO_PATTERN`, beside whatever gate
  its characters fail
  ([`kf318`](../../../a12-rulekit/docs/KERNEL-FINDINGS.md#kf318));
- a String message answering one declared locale and not another, a blank text counting as
  unanswered, draws `MVK_ERROR_MESSAGE_FOR_LANGUAGE_MISSING` on either arm;
- a text carrying a lone surrogate meets the encoding gate first: `WRONG_ENCODING` stands in place of
  the character or parameter class that text would otherwise draw, one per field from the first failing
  declared locale (rows `we-s`, `we-e`, [spec/11](../../spec/11-messages-and-custom.md)). A JSON file
  cannot carry a lone surrogate through a parser that replaces it, so the model reader rewrites each to
  `loneSurrogateStandIn` before parsing and this gate reads that scalar.

Each text's gates are [`StringPatternMessage`](StringPatternMessage.lean)'s; this module owns only
which texts are asked, the pairing classes and the locale class.
-/

namespace A12Kernel

/-- Which declaration a field message belongs to. -/
inductive FieldMessageCarrier where
  | stringPattern
  | stringNoPattern
  | enumerationInvalidValue
  | required
  deriving Repr, DecidableEq

/-- One message entry as the model writes it. -/
structure FieldMessageEntry where
  locale : String
  text : String
  deriving Repr, DecidableEq

/-- The text asked for one locale: the last entry written for it. -/
def FieldMessageEntry.askedFor? (entries : List FieldMessageEntry) (locale : String) :
    Option String :=
  (entries.filter (·.locale == locale)).getLast?.map (·.text)

/-- The scalar the model reader writes in place of a lone UTF-16 surrogate. It is the last Unicode
scalar, so it is outside every repertoire a message may use; the one collision is an authored `U+10FFFF`,
which reads as a lone surrogate. -/
def loneSurrogateStandIn : Char := Char.ofNat 0x10FFFF

/-- A text's named class under the pattern message's gates. An empty text draws none here: whether
a message is there at all is the presence rule's question below. -/
private def fieldMessageTextDiagnostic? (tokens : StringPatternMessageTokens) (text : String) :
    Option KernelStaticDiagnostic :=
  if text.toList.contains loneSurrogateStandIn then some .wrongEncoding
  else match elaborateStringPatternMessageTemplate tokens text with
    | .ok _ | .error .emptyTemplate => none
    | .error error => error.namedStringPatternDiagnostic?

/-- Blank as the rows measure it, on spaces and a tab; the other whitespace characters Lean counts
are unmeasured. -/
private def blankFieldMessage (text : String) : Bool := text.all Char.isWhitespace

/-- Every class one field's messages draw, in the order text, locale, pairing. `reached` is false for
a field the default variant deletes. The presence and locale rules are measured on a String alone;
an Enumeration's or a required field's message meets neither here, which no row measures, and no
row orders a text class against the locale class. -/
def fieldMessageDiagnostics (tokens : StringPatternMessageTokens)
    (declaredLocales : List String) (carrier : FieldMessageCarrier)
    (entries : List FieldMessageEntry) (reached : Bool := true) : List KernelStaticDiagnostic :=
  if !reached || carrier == .required then []
  else
    let asked := declaredLocales.filterMap (FieldMessageEntry.askedFor? entries)
    let textClass := asked.findSome? (fieldMessageTextDiagnostic? tokens)
    let answered := declaredLocales.filter fun locale =>
      (FieldMessageEntry.askedFor? entries locale).any (!blankFieldMessage ·)
    let isString := carrier == .stringPattern || carrier == .stringNoPattern
    let languageMissing := isString && !answered.isEmpty && answered.length < declaredLocales.length
    let pairing := match carrier with
      | .stringPattern => if answered.isEmpty then [.errorMessageAndPatternInvalid] else []
      | .stringNoPattern => if answered.isEmpty then [] else [.errorMessageAndNoPattern]
      | _ => []
    textClass.toList ++ (if languageMissing then [.errorMessageForLanguageMissing] else []) ++ pairing

end A12Kernel
