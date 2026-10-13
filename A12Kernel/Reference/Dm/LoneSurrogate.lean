import Lean.Data.Json
import A12Kernel.Elaboration.FieldMessageCheck

/-! # Reading a DM-JSON file that holds a lone UTF-16 surrogate

A JSON string may escape a lone surrogate (`\ud800`), which no Unicode scalar value can hold, so a
parser either refuses the file or replaces the escape with a character that is indistinguishable from an
authored one. The Kernel reports such a message text as an encoding defect, so the information has to
survive the parse. `replaceLoneSurrogates` rewrites each escape of a surrogate that does not form a
high-low pair into the escape pair of `loneSurrogateStandIn`, which then parses as that one scalar.

The escape scanner treats a backslash and the character after it as one unit, so `\\ud800`, an escaped
backslash followed by text, is left alone. An authored `U+10FFFF`, written raw or as its escape pair, is
read as `U+10FFFE` so that it cannot be taken for a lone surrogate: both are last-plane noncharacters,
which every gate here classes alike, and in a field message both draw the invalid-character class alone
(rows `we-authored`, `we-noncharacter-bmp`), where a lone surrogate draws the encoding class.

It is an input adapter, differentially tested by the field-declaration capture (rows `we-s`, `we-e`,
`we-authored`) and by the examples below, not proved.
-/

namespace A12Kernel.Dm

open Lean A12Kernel

private def hexValue? (character : Char) : Option Nat :=
  if '0' ≤ character && character ≤ '9' then some (character.toNat - '0'.toNat)
  else if 'a' ≤ character && character ≤ 'f' then some (character.toNat - 'a'.toNat + 10)
  else if 'A' ≤ character && character ≤ 'F' then some (character.toNat - 'A'.toNat + 10)
  else none

/-- Four hexadecimal digits at the head of the text, as written, their value and what follows. -/
private def hexFour? : List Char → Option (List Char × Nat × List Char)
  | a :: b :: c :: d :: rest => do
      let value := ((← hexValue? a) * 16 + (← hexValue? b)) * 256 + ((← hexValue? c) * 16 + (← hexValue? d))
      some ([a, b, c, d], value, rest)
  | _ => none

private def isHigh (code : Nat) : Bool := 0xD800 ≤ code && code ≤ 0xDBFF

private def isLow (code : Nat) : Bool := 0xDC00 ≤ code && code ≤ 0xDFFF

/-- The escape pair of `loneSurrogateStandIn`, `U+10FFFF`. -/
private def standInEscape : List Char := "\\uDBFF\\uDFFF".toList

/-- The escape pair of `U+10FFFE`, which an authored `U+10FFFF` is read as. -/
private def authoredMaximumEscape : List Char := "\\uDBFF\\uDFFE".toList

private partial def rewrite : List Char → List Char
  | '\\' :: 'u' :: rest =>
      match hexFour? rest with
      | none => '\\' :: 'u' :: rewrite rest
      | some (digits, code, afterFirst) =>
          if isHigh code then
            match afterFirst with
            | '\\' :: 'u' :: afterEscape =>
                match hexFour? afterEscape with
                | some (lowDigits, low, remaining) =>
                    if isLow low then
                      if code == 0xDBFF && low == 0xDFFF then authoredMaximumEscape ++ rewrite remaining
                      else ['\\', 'u'] ++ digits ++ ['\\', 'u'] ++ lowDigits ++ rewrite remaining
                    else standInEscape ++ rewrite afterFirst
                | none => standInEscape ++ rewrite afterFirst
            | _ => standInEscape ++ rewrite afterFirst
          else if isLow code then standInEscape ++ rewrite afterFirst
          else ['\\', 'u'] ++ digits ++ rewrite afterFirst
  | '\\' :: other :: rest => '\\' :: other :: rewrite rest
  | character :: rest =>
      (if character == loneSurrogateStandIn then Char.ofNat 0x10FFFE else character) :: rewrite rest
  | [] => []

/-- The text with every escaped lone surrogate replaced by the escape pair of `loneSurrogateStandIn`. -/
def replaceLoneSurrogates (text : String) : String := String.ofList (rewrite text.toList)

/-- Parse a DM-JSON file's text, keeping a lone surrogate visible as `loneSurrogateStandIn`. -/
def parseModelJson (text : String) : Except String Json := Json.parse (replaceLoneSurrogates text)

private def parsedString? (json : String) : Option String :=
  match parseModelJson json with
  | .ok (.str value) => some value
  | _ => none

private def stand : String := String.singleton loneSurrogateStandIn

/- A lone high or low surrogate becomes the stand-in, a valid pair is untouched and parses as its
   scalar, a high surrogate followed by anything but a low one is lone, and an escaped backslash
   shields the text after it from the scan. -/
example :
    parsedString? "\"a\\ud800b\"" = some ("a" ++ stand ++ "b") ∧
    parsedString? "\"\\udc00\"" = some stand ∧
    parsedString? "\"\\ud83d\\ude00\"" = some "😀" ∧
    parsedString? "\"\\ud83d\\u0041\"" = some (stand ++ "A") ∧
    parsedString? "\"\\ud800\\ud800\"" = some (stand ++ stand) ∧
    parsedString? "\"\\\\ud800\"" = some "\\ud800" ∧
    parsedString? "\"\\u0041\\uD83D\\uDE00\"" = some "A😀" ∧
    parsedString? "\"\\udbff\\udfff\"" = some (String.singleton (Char.ofNat 0x10FFFE)) ∧
    parsedString? ("\"" ++ stand ++ "\"") = some (String.singleton (Char.ofNat 0x10FFFE)) := by
  native_decide

end A12Kernel.Dm
