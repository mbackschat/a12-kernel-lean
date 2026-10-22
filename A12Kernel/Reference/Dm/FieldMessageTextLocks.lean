import A12Kernel.Reference.Dm.FieldMessageText

/-! # Field-owned message texts

Each expectation is the text the Kernel rendered for the field-owned producer capture
(`docs/sources/message-parameter-rendering-probes.md#src-field-owned-message-producers`), field by
field, on its document whose required fields are empty and whose Enumeration fields hold `Z`. -/

namespace A12Kernel.Dm.FieldMessageTextLocks

open Lean A12Kernel

private def localized (text : String) : Json :=
  Json.arr #[Json.mkObj [("locale", "en_US"), ("text", .str text)]]

private def element (name : String) (fieldType : Json) (members : List (String × Json)) : Json :=
  Json.mkObj [("type", "Field"), ("name", .str name), ("Field", Json.mkObj ([("fieldType", fieldType)] ++ members))]

private def required (name template : String) (label? : Option String := none) : Json :=
  element name (Json.mkObj [("type", "StringType")])
    ([("requirednessConfig", Json.mkObj [("mode", "absoluteOrRelativeToNextRepAncestor"),
        ("errorMessage", localized template)])] ++ (label?.map fun label => ("label", localized label)).toList)

private def requiredText (name template : String) (label? : Option String := none) : Option String :=
  (requirednessMessageText? (required name template label?) "en_US").toOption.join

private def english : StringPatternMessageTokens := { field := "field", fieldValue := "field.value" }

private def enumeration (name template : String) (label? : Option String := none) : Json :=
  element name (Json.mkObj [("type", "EnumerationType"), ("EnumerationType", Json.mkObj [
      ("values", Json.arr #[Json.mkObj [("value", "A")]]), ("errorMessage", localized template)])])
    (label?.map fun label => ("label", localized label)).toList

/-- Both languages' name and value tokens substitute, the label winning over the name; every other
parameter, a doubled dollar and an unclosed pair stay verbatim; a row field renders the same. Rows
`q01`–`q17` and `rq`. -/
example :
    requiredText "q01" "Req $field$ end" "Label q01" = some "Req Label q01 end" ∧
    requiredText "q02" "Req $field.value$ end" = some "Req  end" ∧
    requiredText "q03" "Req $$ $field$" = some "Req $$ q03" ∧
    requiredText "q04" "Req $Feld$" = some "Req q04" ∧
    requiredText "q05" "Req $BaseYear$" = some "Req $BaseYear$" ∧
    requiredText "q07" "Req $field->Cat$" = some "Req $field->Cat$" ∧
    requiredText "q10" "Req $field" = some "Req $field" ∧
    requiredText "q11" "Req $FIELD$" = some "Req $FIELD$" ∧
    requiredText "q12" "Req $field.Wert$" = some "Req $field.Wert$" ∧
    requiredText "q13" "Req $ field $" = some "Req $ field $" ∧
    requiredText "q14" "$$" = some "$$" ∧
    requiredText "q16" "Req $Feld.Wert$ end" = some "Req  end" ∧
    requiredText "q15" "Req $field$ $field.value$" "Label q15" = some "Req Label q15 " ∧
    requiredText "q17" "Req $Feld$ $field$" "Label q17" = some "Req Label q17 Label q17" ∧
    requiredText "rq" "Row $field$ $field.value$" "Row label" = some "Row Row label " := by
  native_decide

/-- Overlapping spellings separate successive replacements from one scan and fix their order. A
single left-to-right scan would render `q21` as the label followed by `Feld$`. Rows `q18`–`q23`. -/
example :
    requiredText "q18" "A$field$field.value$B" "Label q18" = some "ALabel q18field.value$B" ∧
    requiredText "q19" "$field.value$field$" "Label q19" = some "$field.valueLabel q19" ∧
    requiredText "q20" "$Feld$field$" "Label q20" = some "Label q20field$" ∧
    requiredText "q21" "$field$Feld$" "Label q21" = some "$fieldLabel q21" ∧
    requiredText "q22" "$field.value$Feld.Wert$" "Label q22" = some "$field.value" ∧
    requiredText "q23" "$Feld.Wert$field$" "Label q23" = some "$Feld.WertLabel q23" := by
  native_decide

/-- A fifth fixed token, the literal `$<fieldName>.Value$`, is replaced by the empty text before the
other four: `r14` would keep the label after `$field` if it ran last. Each pass reads the running
text, so a token a label carries in meets every later pass: `r10` and `r11`. Peer rows on the Kernel's
dynamic strategy ([inbound](../../../docs/sources/inbound-handbacks.md#src-inbound-2026-10-18)). -/
example :
    requiredText "r13" "r13 $<fieldName>.Value$ end" "Label r13" = some "r13  end" ∧
    requiredText "r14" "r14 $field$<fieldName>.Value$" "Label r14" = some "r14 $field" ∧
    requiredText "r10" "r10 $field$" "Insurer $field.value$ x" = some "r10 Insurer  x" ∧
    requiredText "r11" "r11 $Feld$" "Carrier $field$" = some "r11 Carrier Carrier $field$" := by
  native_decide

/-- An Enumeration's text renders the label and the stored value; it meets the String-pattern grammar,
so an empty pair, `BaseYear`, another field, a category and a wrong case are refused, while a
required field's text draws no class. Rows `n01`–`n07` and `q05`, `q06`, `q10`. -/
example :
    (enumerationMessageText? (enumeration "n01" "Enum $field$ end" "Label n01") english "en_US" "Z").toOption.join =
      some "Enum Label n01 end" ∧
    (enumerationMessageText? (enumeration "n02" "Enum $field.value$ end") english "en_US" "Z").toOption.join =
      some "Enum Z end" ∧
    (["Enum $$ x", "Enum $BaseYear$", "Enum $Other$", "Enum $field->Cat$", "Enum $FIELD$"].map fun text =>
      (fieldMessageDiagnostics english ["en_US"] .enumerationInvalidValue [{ locale := "en_US", text }]).map
        (·.kernelCode)) = List.replicate 5 ["INVALID_PARAMETER"] ∧
    (["Req $BaseYear$", "Req $Other$", "Req $field"].all fun text =>
      (fieldMessageDiagnostics english ["en_US"] .required [{ locale := "en_US", text }]).isEmpty) := by
  native_decide

end A12Kernel.Dm.FieldMessageTextLocks
