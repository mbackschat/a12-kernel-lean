import A12Kernel.Elaboration.StringPatternMessage
import A12Kernel.Elaboration.ValidationMessageDiagnostic

/-! # en_US String-pattern producer conformance locks

The two admitted tokens against stylized and actual names, its rejected empty parameter, and the
delimiter gate it shares with the rule producer. -/

namespace A12Kernel.Conformance.StringPatternMessage

open A12Kernel

private def stringPatternInputs : StringPatternMessageInputs where
  fieldName := "Code"
  fieldValue := "$field$"

private def stringPatternRender? (template : String) : Option ResolvedMessageText := do
  let checked ←
    (elaborateEnUsStringPatternMessageTemplate template).toOption
  pure (checked.renderError stringPatternInputs).text

private def stringPatternTemplateError? (template : String) :
    Option ValidationMessageTemplateError :=
  match elaborateEnUsStringPatternMessageTemplate template with
  | .ok _ => none
  | .error error => some error

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

/- A parameter other than the two tokens draws `INVALID_PARAMETER`, measured for the stylized and the
   actual field name ([ledger](../../docs/archived/A12-DMKITS-SPEC-SYNC-LEDGER-THROUGH-2026-08-28.md#exp-2026-07-30-01)).
   The empty pair is refused too, but that disposition names no class for it, so it claims none. -/
example :
    stringPatternNamedDiagnostic? "$Field$" = some (some "INVALID_PARAMETER") ∧
    stringPatternNamedDiagnostic? "$Code$" = some (some "INVALID_PARAMETER") ∧
    stringPatternNamedDiagnostic? "Cost $$ $field$" = some none := by
  native_decide

end A12Kernel.Conformance.StringPatternMessage
