/-! # A12Kernel.Semantics.String — shared String primitives -/

namespace A12Kernel

/-- Replace every non-overlapping CRLF pair with LF in one left-to-right ingestion pass. -/
def normalizeCrlfCharacters : List Char → List Char
  | [] => []
  | '\r' :: '\n' :: rest => '\n' :: normalizeCrlfCharacters rest
  | character :: rest => character :: normalizeCrlfCharacters rest

/-- Produce the evaluated String cached when an admitted parsed input enters formal checking. Raw storage and line-break permission are outside this reduced operation. -/
def normalizeEvaluatedString (value : String) : String :=
  String.ofList (normalizeCrlfCharacters value.toList)

/-- Count UTF-16 code units, matching the JVM/JavaScript kernel boundary rather than Unicode scalar values or grapheme clusters. -/
def utf16CodeUnitLength (value : String) : Nat :=
  value.foldl (fun units character =>
    units + if character.toNat < 0x10000 then 1 else 2) 0

/-- Split a scalar String at an exact UTF-16 code-unit boundary. Lean Strings cannot represent a cut through one surrogate pair, so such an offset fails closed. -/
def splitAtUtf16CodeUnits : List Char → Nat → Option (List Char × List Char)
  | characters, 0 => some ([], characters)
  | [], _ + 1 => none
  | character :: rest, units + 1 =>
      if character.toNat < 0x10000 then
        match splitAtUtf16CodeUnits rest units with
        | some (before, suffix) => some (character :: before, suffix)
        | none => none
      else
        match units with
        | 0 => none
        | remaining + 1 =>
            match splitAtUtf16CodeUnits rest remaining with
            | some (before, suffix) => some (character :: before, suffix)
            | none => none

/-- Extract one zero-based, end-exclusive UTF-16 slice when both offsets are scalar boundaries and lie inside the String. -/
def utf16CodeUnitSlice? (value : String) (start finish : Nat) : Option String :=
  if start ≤ finish then
    match splitAtUtf16CodeUnits value.toList start with
    | none => none
    | some (_, fromStart) =>
        match splitAtUtf16CodeUnits fromStart (finish - start) with
        | none => none
        | some (selected, _) => some (String.ofList selected)
  else
    none

/-- Whether authored 1-based inclusive String-range bounds form the statically legal interval consumed by both range operations. -/
def validStringRange (start finish : Nat) : Bool :=
  0 < start && start ≤ finish

/-- Parse one nonempty ASCII digit sequence as an unbounded natural number. This is deliberately narrower than locale or signed decimal parsing. -/
private def parseAsciiNaturalAux (accumulator : Nat) : List Char → Option Nat
  | [] => some accumulator
  | character :: rest =>
      let code := character.toNat
      if _digit : 48 ≤ code ∧ code ≤ 57 then
        parseAsciiNaturalAux (accumulator * 10 + (code - 48)) rest
      else
        none

/-- Parse exactly Java/TypeScript `\d+`'s ASCII subset used by the range-to-Number operation. Empty, signed, fractional, and otherwise non-digit text fails. -/
def parseAsciiNatural? (value : String) : Option Nat :=
  match value.toList with
  | [] => none
  | characters => parseAsciiNaturalAux 0 characters

/-- Starts of the ten-code-point BMP decimal blocks accepted by Java 21's `Character.isDigit(char)`. The `char` overload rejects supplementary-plane decimal code points because it observes their surrogate code units separately. -/
private def java21BmpDecimalDigitStarts : List Nat :=
  [0x0030, 0x0660, 0x06F0, 0x07C0, 0x0966, 0x09E6, 0x0A66, 0x0AE6,
   0x0B66, 0x0BE6, 0x0C66, 0x0CE6, 0x0D66, 0x0DE6, 0x0E50, 0x0ED0,
   0x0F20, 0x1040, 0x1090, 0x17E0, 0x1810, 0x1946, 0x19D0, 0x1A80,
   0x1A90, 0x1B50, 0x1BB0, 0x1C40, 0x1C50, 0xA620, 0xA8D0, 0xA900,
   0xA9D0, 0xA9F0, 0xAA50, 0xABF0, 0xFF10]

private def java21BmpDecimalDigitValueFrom? (code : Nat) :
    List Nat → Option Nat
  | [] => none
  | start :: rest =>
      if start ≤ code ∧ code < start + 10 then
        some (code - start)
      else
        java21BmpDecimalDigitValueFrom? code rest

/-- Decimal value under the exact Java 21 UTF-16 `Character.isDigit(char)` profile used by the pinned Kernel's Commons Lang parser. -/
def java21BmpDecimalDigitValue? (character : Char) : Option Nat :=
  java21BmpDecimalDigitValueFrom?
    character.toNat java21BmpDecimalDigitStarts

private def parseJava21BmpNaturalAux (accumulator : Nat) :
    List Char → Option Nat
  | [] => some accumulator
  | character :: rest => do
      let digit ← java21BmpDecimalDigitValue? character
      parseJava21BmpNaturalAux (accumulator * 10 + digit) rest

/-- Parse one nonempty natural-number token under the pinned Java 21 per-UTF-16-code-unit decimal-digit profile. -/
def parseJava21BmpNatural? (value : String) : Option Nat :=
  match value.toList with
  | [] => none
  | characters => parseJava21BmpNaturalAux 0 characters

/-- The exact declared Java-pattern source whose complete runtime language is already executable without embedding a regex engine. This is model metadata, not a `FieldValueAsNumber` eligibility flag. -/
def asciiDigitsPatternSource : String := "[0-9]+"

/-- Execute the one declaration-pattern profile whose Java whole-value meaning is a nonempty sequence of ASCII decimal characters. This predicate deliberately avoids constructing an unbounded number merely to classify a String. Other admitted Java patterns remain behind the injected pattern capability and fail closed at checked String-value lowering. -/
def matchesAsciiDigitsPattern (value : String) : Bool :=
  match value.toList with
  | [] => false
  | characters => characters.all fun character =>
      let code := character.toNat
      48 ≤ code && code ≤ 57

/-- Apply the checked operation's 1-based inclusive UTF-16 range and digits-only numeric conversion. Invalid bounds, overshoot, non-digits, and an unrepresentable half-surrogate slice all yield zero; checked lowering separately makes invalid bounds unreachable. -/
def utf16RangeAsNatural (value : String) (start finish : Nat) : Nat :=
  if !validStringRange start finish || utf16CodeUnitLength value < finish then
    0
  else
    match utf16CodeUnitSlice? value (start - 1) finish with
    | some selected => (parseAsciiNatural? selected).getD 0
    | none => 0

/-- Whether a String contains a CR or LF code point. Declaration-owned formal and computed-target checking consume this before normalization and length measurement. -/
def containsLineBreak (value : String) : Bool :=
  value.any fun character => character == '\r' || character == '\n'

end A12Kernel
