import A12Kernel.Elaboration.FieldMessageCheck

/-! # Locks on which classes a field's own messages draw

Every row is the peer's `FieldTypeMessageTextLawsTest`, each model checked by the Kernel
([inbound](../../docs/sources/inbound-handbacks.md#inbound-2026-09-26n-field-message-gates),
[inbound](../../docs/sources/inbound-handbacks.md#inbound-2026-09-27a-field-message-render)). An empty list is an
admitted field. The texts carry a tab (`INVALID_CHARACTERS`) or a line feed (`INVALID_LINEBREAK`)
so each row names the locale that was asked.
-/

namespace A12Kernel.Conformance.FieldMessageCheck

open A12Kernel

private def english : StringPatternMessageTokens := { field := "field", fieldValue := "field.value" }

private def check (declared : List String) (carrier : FieldMessageCarrier)
    (entries : List (String × String)) (reached : Bool := true) : List String :=
  (fieldMessageDiagnostics english declared carrier
    (entries.map fun (locale, text) => { locale, text }) reached).map (·.kernelCode)

private def both : List String := ["en_US", "de_DE"]

/- Every declared locale reports its own text's class, in the order the model declares the locales: the
   declared order decides, the written order does not, and a locale alone defective still reports
   (the peer's two-by-two and its entry-order rows). Kernel 30.8.1 reported the first failing locale only.
   Locked: a12-dmkits FieldTypeMessageTextLawsTest at 1124b523f, kernel 31.1.1. -/
example :
    check both .stringPattern [("en_US", "a\tb"), ("de_DE", "a\nb")] =
      ["INVALID_CHARACTERS", "INVALID_LINEBREAK"] ∧
    check ["de_DE", "en_US"] .stringPattern [("en_US", "a\tb"), ("de_DE", "a\nb")] =
      ["INVALID_LINEBREAK", "INVALID_CHARACTERS"] ∧
    check ["de_DE", "en_US"] .stringPattern [("de_DE", "a\nb"), ("en_US", "a\tb")] =
      ["INVALID_LINEBREAK", "INVALID_CHARACTERS"] ∧
    check both .stringPattern [("de_DE", "a\nb"), ("en_US", "a\tb")] =
      ["INVALID_CHARACTERS", "INVALID_LINEBREAK"] ∧
    check both .stringPattern [("en_US", "ab"), ("de_DE", "a\tb")] = ["INVALID_CHARACTERS"] := by
  native_decide

private def cp (value : Nat) : String := String.singleton (Char.ofNat value)

private def lone : String := String.singleton loneSurrogateStandIn

/- The peer's character-gate grid on a field type's own message, row for row: the line break first, then the
   encoding, then `\p{C}`, each withholding the gates after it, so the lone surrogate is `WRONG_ENCODING`
   unless a line separator stands beside it. A supplementary scalar outside `\p{C}` draws no class here; its
   codeless refusal is the notification layer's. Kernel 30.8.1 asked the encoding before the line break.
   Locked: a12-dmkits ErrorTextCharacterGateLawsTest at 1124b523f, kernel 31.1.1; the tab beside a lone surrogate
   is derived from that order, unmeasured. -/
example :
    ([("plain", "plain", []), ("U+2028", "a" ++ cp 0x2028 ++ "b", ["INVALID_LINEBREAK"]),
      ("U+2029", "a" ++ cp 0x2029 ++ "b", ["INVALID_LINEBREAK"]), ("line feed", "a\nb", ["INVALID_LINEBREAK"]),
      ("tab", "a\tb", ["INVALID_CHARACTERS"]), ("U+0085", "a" ++ cp 0x0085 ++ "b", ["INVALID_CHARACTERS"]),
      ("U+200B", "a" ++ cp 0x200B ++ "b", ["INVALID_CHARACTERS"]),
      ("U+00AD", "a" ++ cp 0x00AD ++ "b", ["INVALID_CHARACTERS"]),
      ("U+FEFF", "a" ++ cp 0xFEFF ++ "b", ["INVALID_CHARACTERS"]),
      ("U+200E", "a" ++ cp 0x200E ++ "b", ["INVALID_CHARACTERS"]),
      ("U+E000", "a" ++ cp 0xE000 ++ "b", ["INVALID_CHARACTERS"]),
      ("U+0378", "a" ++ cp 0x0378 ++ "b", ["INVALID_CHARACTERS"]),
      ("U+00A0", "a" ++ cp 0x00A0 ++ "b", []),
      ("lone surrogate", "a" ++ lone ++ "b", ["WRONG_ENCODING"]),
      ("supplementary private use", "a" ++ cp 0xF0000 ++ "b", ["INVALID_CHARACTERS"]),
      ("supplementary outside C", "a" ++ cp 0x1F600 ++ "b", []),
      ("U+E0001", "a" ++ cp 0xE0001 ++ "b", ["INVALID_CHARACTERS"]),
      ("U+2028 beside tab", "a\tb" ++ cp 0x2028 ++ "c", ["INVALID_LINEBREAK"]),
      ("line feed beside lone surrogate", "a\nb" ++ lone ++ "c", ["INVALID_LINEBREAK"]),
      ("tab beside lone surrogate", "a\tb" ++ lone ++ "c", ["WRONG_ENCODING"])].all
      fun (_, text, expected) =>
        check ["en_US"] .stringPattern [("en_US", text)] == expected &&
        check ["en_US"] .enumerationInvalidValue [("en_US", text)] == expected) := by
  native_decide

/- The later of two entries for one locale is asked, an undeclared locale never is, and an empty
   patterned text draws the pattern's pairing class rather than a character gate. -/
example :
    check ["en_US"] .stringPattern [("en_US", "a\tb"), ("en_US", "capitals only")] = [] ∧
    check ["en_US"] .stringPattern [("en_US", "capitals only"), ("en_US", "a\tb")] =
      ["INVALID_CHARACTERS"] ∧
    check ["en_US"] .stringPattern [("en_US", "capitals only"), ("fr_FR", "a\tb")] = [] ∧
    check ["en_US"] .stringPattern [("en_US", "")] = ["MVK_ERROR_MESSAGE_AND_PATTERN_INVALID"] := by
  native_decide

/- The Enumeration's invalid-value text meets the same gates; a required field's text meets none,
   and a field whose messages are withheld is never reached. -/
example :
    check ["en_US"] .enumerationInvalidValue [("en_US", "a\tb")] = ["INVALID_CHARACTERS"] ∧
    check ["en_US"] .enumerationInvalidValue [("en_US", "$Status$ is not allowed")] =
      ["INVALID_PARAMETER"] ∧
    check ["en_US"] .enumerationInvalidValue [("en_US", "$field$ is not allowed")] = [] ∧
    check ["en_US"] .required [("en_US", "a\tb")] = [] ∧
    check ["en_US"] .stringPattern [("en_US", "a\tb")] (reached := false) = [] := by
  native_decide

/- With no pattern, the pairing class needs a text that is not blank and a declared locale, and it
   stands beside the character gate: an empty or single-space text is admitted and a tab-only one
   draws the character class alone. -/
example :
    check ["en_US"] .stringNoPattern [] = [] ∧
    check ["en_US"] .stringNoPattern [("en_US", "capitals")] =
      ["MVK_ERROR_MESSAGE_AND_NO_PATTERN"] ∧
    check ["en_US"] .stringNoPattern [("fr_FR", "capitals")] = [] ∧
    check ["en_US"] .stringNoPattern [("en_US", "")] = [] ∧
    check ["en_US"] .stringNoPattern [("en_US", " ")] = [] ∧
    check ["en_US"] .stringNoPattern [("en_US", "\t")] = ["INVALID_CHARACTERS"] ∧
    check ["en_US"] .stringNoPattern [("en_US", "a\tb")] =
      ["INVALID_CHARACTERS", "MVK_ERROR_MESSAGE_AND_NO_PATTERN"] := by
  native_decide

/- A pattern and its message require each other, and a message counts only as non-blank text for a
   declared locale: no entry, a blank text and an undeclared locale's text all refuse a pattern with
   its own class and are admitted without one (peer `StringTypeMessageAndPatternLawsTest`,
   [`kf318`](../../../a12-rulekit/docs/KERNEL-FINDINGS.md#kf318)). -/
example :
    check ["en_US"] .stringPattern [] = ["MVK_ERROR_MESSAGE_AND_PATTERN_INVALID"] ∧
    check ["en_US"] .stringPattern [("en_US", "   ")] = ["MVK_ERROR_MESSAGE_AND_PATTERN_INVALID"] ∧
    check ["en_US"] .stringPattern [("de_DE", "fehlerhaft")] =
      ["MVK_ERROR_MESSAGE_AND_PATTERN_INVALID"] ∧
    check ["en_US"] .stringNoPattern [("en_US", "   ")] = [] ∧
    check ["en_US"] .stringNoPattern [("de_DE", "fehlerhaft")] = [] := by
  native_decide

/- Once one declared locale is answered and another is not, the message draws the locale class on
   either arm, a blank text counting as unanswered. -/
example :
    check both .stringPattern [("en_US", "malformed"), ("de_DE", "fehlerhaft")] = [] ∧
    check both .stringPattern [("en_US", "malformed")] = ["MVK_ERROR_MESSAGE_FOR_LANGUAGE_MISSING"] ∧
    check both .stringPattern [("de_DE", "fehlerhaft")] = ["MVK_ERROR_MESSAGE_FOR_LANGUAGE_MISSING"] ∧
    check both .stringPattern [("en_US", "malformed"), ("de_DE", "   ")] =
      ["MVK_ERROR_MESSAGE_FOR_LANGUAGE_MISSING"] ∧
    check both .stringPattern [("fr_FR", "mal forme")] = ["MVK_ERROR_MESSAGE_AND_PATTERN_INVALID"] ∧
    check both .stringNoPattern [("en_US", "malformed")] =
      ["MVK_ERROR_MESSAGE_FOR_LANGUAGE_MISSING", "MVK_ERROR_MESSAGE_AND_NO_PATTERN"] := by
  native_decide

end A12Kernel.Conformance.FieldMessageCheck
