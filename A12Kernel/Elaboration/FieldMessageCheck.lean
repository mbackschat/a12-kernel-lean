import A12Kernel.Elaboration.StringPatternMessage
import A12Kernel.Elaboration.ValidationMessageDiagnostic

/-! # Which classes a field's own messages draw

A field declaration can carry its own message per locale: a String pattern's invalid-value text, an
Enumeration's invalid-value text, a required field's text, or a String text with no pattern to pair.
The model check reads them as one field, not one text at a time
([`spec/11`](../../spec/11-messages-and-custom.md),
[inbound](../../docs/SOURCES.md#inbound-2026-09-26n-field-message-gates),
[inbound](../../docs/SOURCES.md#inbound-2026-09-27a-field-message-render)):

- the locales are asked **in the order the model declares them**, whatever order the entries are
  written in, and a locale the model does not declare is never asked;
- of two entries for one locale the **later** is asked;
- the texts meet the pattern message's lexical and parameter gates, and only the **first** failing
  locale reports;
- a required field's own text meets no gate, and a field its own `ONLY` filter deletes is never
  reached;
- a String text with no pattern also draws the **pairing class**, once, when the text asked is not
  blank, beside whatever gate its characters fail.

Each text's gates are [`StringPatternMessage`](StringPatternMessage.lean)'s; this module owns only
which texts are asked and the pairing class.
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

/-- A text's named class under the pattern message's gates. The empty text's pairing class belongs
to a patterned String alone: with no pattern an empty text is admitted, and no row measures an empty
Enumeration text, so that carrier answers nothing for it. -/
private def fieldMessageTextDiagnostic? (tokens : StringPatternMessageTokens)
    (carrier : FieldMessageCarrier) (text : String) : Option KernelStaticDiagnostic :=
  match elaborateStringPatternMessageTemplate tokens text with
  | .ok _ => none
  | .error .emptyTemplate => if carrier == .stringPattern then some .errorMessageAndPatternInvalid else none
  | .error error => error.namedStringPatternDiagnostic?

/-- Every class one field's messages draw, the text's class first. `reached` is false for a field
the default variant deletes. Which asked text decides the pairing class when several locales are
declared is unmeasured; any non-blank one draws it here. -/
def fieldMessageDiagnostics (tokens : StringPatternMessageTokens)
    (declaredLocales : List String) (carrier : FieldMessageCarrier)
    (entries : List FieldMessageEntry) (reached : Bool := true) : List KernelStaticDiagnostic :=
  if !reached || carrier == .required then []
  else
    let asked := declaredLocales.filterMap (FieldMessageEntry.askedFor? entries)
    let textClass := asked.findSome? (fieldMessageTextDiagnostic? tokens carrier)
    let pairing := carrier == .stringNoPattern && asked.any (!·.all Char.isWhitespace)
    textClass.toList ++ (if pairing then [.errorMessageAndNoPattern] else [])

end A12Kernel
