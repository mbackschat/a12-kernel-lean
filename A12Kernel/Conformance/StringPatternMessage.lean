import A12Kernel.Elaboration.StringPatternMessage
import A12Kernel.Elaboration.ValidationMessageDiagnostic

/-! # String-pattern producer conformance locks

The two admitted tokens in each condition language against stylized and actual names, the dollar
pieces Java's `split` reads, and the gates it shares with the rule producer. -/

namespace A12Kernel.Conformance.StringPatternMessage

open A12Kernel

private def stringPatternInputs : StringPatternMessageInputs where
  fieldName := "Code"
  fieldValue := "$field$"

private def english : StringPatternMessageTokens := { field := "field", fieldValue := "field.value" }

private def german : StringPatternMessageTokens := { field := "Feld", fieldValue := "Feld.Wert" }

private def stringPatternRender? (template : String) : Option ResolvedMessageText := do
  let checked ←
    (elaborateStringPatternMessageTemplate english template).toOption
  pure (checked.renderError stringPatternInputs).text

private def stringPatternTemplateErrorIn? (tokens : StringPatternMessageTokens) (template : String) :
    Option ValidationMessageTemplateError :=
  match elaborateStringPatternMessageTemplate tokens template with
  | .ok _ => none
  | .error error => some error

private def stringPatternTemplateError? (template : String) : Option ValidationMessageTemplateError :=
  stringPatternTemplateErrorIn? english template

example :
    stringPatternRender? "$field$" =
        some { text := "Code" } ∧
      stringPatternRender? "Value [$field.value$]" =
        some { text := "Value [$field$]" } := by
  native_decide

example :
    stringPatternTemplateError? "$Field$" =
        some (.invalidParameter "Field") ∧
      stringPatternTemplateError? "$Code$" =
        some (.invalidParameter "Code") ∧
      stringPatternTemplateError? "Cost $$ $field$" =
        some (.invalidParameter "") ∧
      stringPatternTemplateError? "$field" =
        some .oddDollarCount := by
  native_decide

private def cp (value : Nat) : String := String.singleton (Char.ofNat value)

private def stringPatternNamedDiagnostic? (template : String) : Option (Option String) :=
  (stringPatternTemplateError? template).map fun error =>
    error.namedStringPatternDiagnostic?.map KernelStaticDiagnostic.kernelCode

/- **The field's own message meets the rule message's two character gates, line before control**
   ([inbound](../../docs/SOURCES.md#inbound-2026-09-26m-message-characters)). Each row sits in the one
   declared locale's message of a `[A-Z]+` pattern. Beside the line feed the Kernel also reports a
   codeless line-break finding, as it does beside a rule message's line feed; that finding is not this
   projection's. The supplementary scalar is the codeless repertoire refusal alone, so it projects no
   class. -/
example :
    ["a\nb", "a" ++ cp 0x2028 ++ "b", "a" ++ cp 0x2029 ++ "b", "a\tb" ++ cp 0x2028 ++ "c",
        "a\tb", "a" ++ cp 0x0085 ++ "b", "a" ++ cp 0x200B ++ "b", "a" ++ cp 0x00AD ++ "b",
        "a" ++ cp 0x1F600 ++ "b"].map stringPatternNamedDiagnostic? =
      [some (some "INVALID_LINEBREAK"), some (some "INVALID_LINEBREAK"),
       some (some "INVALID_LINEBREAK"), some (some "INVALID_LINEBREAK"),
       some (some "INVALID_CHARACTERS"), some (some "INVALID_CHARACTERS"),
       some (some "INVALID_CHARACTERS"), some (some "INVALID_CHARACTERS"), some none] ∧
    stringPatternTemplateError? ("a" ++ cp 0x00A0 ++ "b") = none := by
  native_decide

/- The field's message meets the same `\p{C}` set, and its refusal of a supplementary character stands
   beside the named class the text draws, as on a rule's message
   ([inbound](../../docs/SOURCES.md#inbound-2026-09-26m-message-characters)). -/
example :
    ["a" ++ cp 0xFEFF ++ "b", "a" ++ cp 0x200E ++ "b", "a" ++ cp 0xE000 ++ "b",
        "a" ++ cp 0x0378 ++ "b", "a" ++ cp 0xF0000 ++ "b", "a" ++ cp 0xE0001 ++ "b"].map
        stringPatternNamedDiagnostic? =
      List.replicate 6 (some (some "INVALID_CHARACTERS")) ∧
    stringPatternTemplateError? ("a" ++ cp 0xF0000 ++ "b") =
      some (.unsupportedCharacterWithError (Char.ofNat 0xF0000) (.controlCharacter (Char.ofNat 0xF0000))) ∧
    stringPatternTemplateError? ("a" ++ cp 0x1F600 ++ "b") =
      some (.unsupportedCharacter (Char.ofNat 0x1F600)) := by
  native_decide

/- The gates beyond the characters, in the Kernel's order: dollar parity ahead of the parameters, the
   character gates ahead of both, and every parameter other than the two tokens, the empty one included,
   `INVALID_PARAMETER` ([ledger](../../docs/archived/A12-DMKITS-SPEC-SYNC-LEDGER-THROUGH-2026-08-28.md#exp-2026-07-30-01),
   [inbound](../../docs/SOURCES.md#inbound-2026-09-26n-field-message-gates)). The German spelling is a
   wrong name in an English model. An empty text is the pairing class, not a character one. -/
example :
    ["capitals only", "$field$ takes capitals", "$field.value$ is not capitals",
        "$field$$field.value$"].all (fun text => stringPatternTemplateError? text == none) ∧
    ["$field takes capitals", "$Field$ takes capitals", "$Code$ takes capitals", "cost $$ in capitals",
        "$Feld$ takes capitals", "$field\ttakes capitals", "$Code$ and $field", ""].map
        stringPatternNamedDiagnostic? =
      [some (some "WRONG_NUMBER_OF_DOLLARS"), some (some "INVALID_PARAMETER"),
       some (some "INVALID_PARAMETER"), some (some "INVALID_PARAMETER"),
       some (some "INVALID_PARAMETER"), some (some "INVALID_CHARACTERS"),
       some (some "WRONG_NUMBER_OF_DOLLARS"), some (some "MVK_ERROR_MESSAGE_AND_PATTERN_INVALID")] := by
  native_decide

/- The tokens follow the model's condition language and not the message's locale: under a German one
   `$Feld$` and `$Feld.Wert$` are admitted and `$field$` is the wrong name. -/
example :
    stringPatternTemplateErrorIn? german "$Feld$ takes capitals" = none ∧
    stringPatternTemplateErrorIn? german "$Feld.Wert$ is not capitals" = none ∧
    stringPatternTemplateErrorIn? german "$field$ takes capitals" =
      some (.invalidParameter "field") := by
  native_decide

/- **The parameters are Java's `split` pieces, whose trailing empty pieces are dropped**: an empty pair at
   the very end, or alone, names no parameter and is admitted, where the same pair at the start is an
   empty parameter. The admitted pair renders as literal dollars by the assumption the module states,
   since no row reads its rendering. -/
example :
    stringPatternTemplateError? "capitals only $$" = none ∧
    stringPatternTemplateError? "$$" = none ∧
    stringPatternTemplateError? "$$ capitals only" = some (.invalidParameter "") ∧
    stringPatternRender? "capitals only $$" = some { text := "capitals only $$" } ∧
    stringPatternRender? "$field$$$" = some { text := "Code$$" } := by
  native_decide

end A12Kernel.Conformance.StringPatternMessage
