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

/-- Whether a String contains a CR or LF code point. Declaration-owned formal and computed-target checking consume this before normalization and length measurement. -/
def containsLineBreak (value : String) : Bool :=
  value.any fun character => character == '\r' || character == '\n'

end A12Kernel
