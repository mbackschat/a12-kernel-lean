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

/-- Whether a declared Date/Time component pattern is one of the checker's four unbounded digit forms or the two forms fixed to the position's stored width. This recognizes exact source spellings, not regular-expression equivalence. -/
def isTemporalComponentDigitPattern (width : Nat) (source : String) : Bool :=
  source == "[0-9]+" ||
    source == "[0-9]*" ||
    source == "\\d+" ||
    source == "\\d*" ||
    source == "[0-9]{" ++ toString width ++ "}" ||
    source == "\\d{" ++ toString width ++ "}"

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

/-- Decode the at-most-four-code-unit String components admitted by Date/Time declarations.
The kernel converts their stored text through BigDecimal (comma normalized to dot), then
`intValue`: truncate toward zero and retain the signed low 32 bits (spec/05 §3). Width bounds
make every mantissa exact under the host precision; this is not a general decimal parser. -/
def parseTemporalComponentInt32? (text : String) : Option Int := do
  if utf16CodeUnitLength text > 4 then none else do
    let signed (chars : List Char) : Bool × List Char := match chars with
      | '-' :: rest => (true, rest)
      | '+' :: rest => (false, rest)
      | rest => (false, rest)
    let (negative, chars) := signed text.toList
    let (mantissa, suffix) := chars.span (fun c => c != 'e' && c != 'E')
    let exponent : Int ← match suffix with
      | [] => some 0
      | _ :: rest => do
          let (negative, digits) := signed rest
          let magnitude ← parseJava21BmpNatural? (String.ofList digits)
          pure (if negative then -(magnitude : Int) else magnitude)
    let (whole, decimal) := mantissa.span (fun c => c != '.' && c != ',')
    let fraction := match decimal with | [] => [] | _ :: rest => rest
    let magnitude ← parseJava21BmpNatural? (String.ofList (whole ++ fraction))
    let unscaled : Int := if negative then -(magnitude : Int) else magnitude
    let power := exponent - (fraction.length : Int)
    let integer := if power < 0 then unscaled.tdiv (10 ^ power.natAbs)
      else unscaled * 10 ^ power.toNat
    pure (Int32.ofInt integer).toInt

/-- The ASCII decimal profile is model metadata, not a `FieldValueAsNumber` eligibility flag. -/
def asciiDigitsPatternSource : String := "[0-9]+"

def asciiUppercasePatternSource : String := "[A-Z]+"

/-- Whole-value range matching requires at least one character; the closed ASCII profiles need neither numeric parsing nor a regex engine. -/
def matchesNonemptyCodePointRange (lower upper : Nat) (value : String) : Bool :=
  match value.toList with
  | [] => false
  | characters => characters.all fun character =>
      let code := character.toNat
      lower ≤ code && code ≤ upper

def matchesAsciiDigitsPattern (value : String) : Bool :=
  matchesNonemptyCodePointRange 48 57 value

def matchesAsciiUppercasePattern (value : String) : Bool :=
  matchesNonemptyCodePointRange 65 90 value

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
