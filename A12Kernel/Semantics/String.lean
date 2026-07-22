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

/-- Whether a String contains a CR or LF code point. Declaration-owned formal and computed-target checking consume this before normalization and length measurement. -/
def containsLineBreak (value : String) : Bool :=
  value.any fun character => character == '\r' || character == '\n'

end A12Kernel
