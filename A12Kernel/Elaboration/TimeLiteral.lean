import A12Kernel.Core
import A12Kernel.Semantics.String

/-! # Checked Time literals

This capsule mirrors the parser's exact `HH:mm:ss` Time-literal boundary. A valid literal is eight ASCII characters with fixed two-digit components and a real whole-second clock. Checking finishes before generated evaluation, so invalid text has no runtime result; every admitted literal erases directly to the existing `TimeOfDay`.

The runtime represents that clock on 1970-01-01 in the model zone, but the admitted DateTime consumer reads only its hour, minute, and second. Locale, model-zone selection, stored-Time formats, and general temporal-expression lowering remain separate.
-/

namespace A12Kernel

private def parseTwoAsciiDigits? (text : String) : Option Nat :=
  if text.length = 2 then parseAsciiNatural? text else none

/-- Decode exactly one parser-admitted ASCII `HH:mm:ss` literal. -/
def decodeTimeLiteral? (source : String) : Option TimeOfDay :=
  match source.splitOn ":" with
  | [hourText, minuteText, secondText] => do
      let hour ← parseTwoAsciiDigits? hourText
      let minute ← parseTwoAsciiDigits? minuteText
      let second ← parseTwoAsciiDigits? secondText
      TimeOfDay.ofHms? hour minute second
  | _ => none

/-- Static Time-literal rejection. The Kernel reports one invalid-date-string class for lexical and clock-reality failures. -/
inductive TimeLiteralElabError where
  | invalidLiteral (source : String)
  deriving Repr, DecidableEq

/-- Check a raw authored literal once and return only its decoded whole-second clock. -/
def elaborateTimeLiteral (source : String) :
    Except TimeLiteralElabError TimeOfDay :=
  match decodeTimeLiteral? source with
  | some time => .ok time
  | none => .error (.invalidLiteral source)

end A12Kernel
