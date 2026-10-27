/-! # The requiredness field-message producer

A required field's own message (`requirednessConfig.errorMessage`) is a third field-owned producer,
distinct from the String-pattern and Enumeration texts and from a rule's error text. The Kernel checks
none of its parameters: every text is admitted, and rendering substitutes five fixed tokens, the
literal `$<fieldName>.Value$` and the English and German spellings of the field and of its value,
whatever else the text holds. Anything else, an unknown or malformed parameter and a `$$` pair
included, stays verbatim.

The substitution is five successive replacements over the whole text, not one left-to-right scan:
`$<fieldName>.Value$`, then `$Feld$`, then `$field$`, then `$Feld.Wert$`, then `$field.value$`.
Overlapping spellings separate the two accounts and fix that order: `$field$Feld$` keeps `$field`
before the name (`docs/sources/message-parameter-rendering-probes.md#src-field-owned-message-producers`),
and `$field$<fieldName>.Value$` keeps `$field` alone, the peer's row `r14`
(`docs/sources/inbound-handbacks.md#src-inbound-2026-10-18`). Whether the field's own name in place of
`<fieldName>` is replaced is unmeasured. The producer
fires only on an empty field, so the value is always the empty text. Both spellings substitute in a
model of either condition language, as spec/11 A.13 states.

A field without a template takes the catalog's default text, a host input this module does not name. -/

namespace A12Kernel

/-- How the Kernel's own full validation names the owning field in a field-owned message when no
display provider is configured: the field's declared label for the message locale when it is
nonempty, otherwise its short name. -/
def fieldOwnedDisplayName (label? : Option String) (name : String) : String :=
  match label? with
  | some label => if label.isEmpty then name else label
  | none => name

/-- Render an authored requiredness message for the field displayed as `displayName`. -/
def renderRequirednessMessage (template displayName : String) : String :=
  ((((template.replace "$<fieldName>.Value$" "").replace "$Feld$" displayName).replace "$field$"
    displayName).replace "$Feld.Wert$" "").replace "$field.value$" ""

end A12Kernel
