import Lean.Data.Json
import A12Kernel.Semantics.String
import A12Kernel.Elaboration.DeclarationAdmission

/-! # How the Kernel's DM-JSON binding reads a member that is not text

The Kernel deserializes a model into Java objects before any consistency check, so a member it cannot
bind leaves no model at all: that is a read failure here, never a Kernel class. Two laws cover every
non-text member measured, on every carrier the a12-dmkits handbacks of 2026-10-18 and 2026-10-21 name
(`docs/sources/inbound-handbacks.md#src-inbound-2026-10-18`, `#src-inbound-2026-10-21`), as kernel
31.1.1's Jackson 3 binds them (a12-dmkits `BooleanMemberBindingDiffTest`, `FieldTypeIntMemberBindingDiffTest`
and `RepeatabilityTextReadingDiffTest` at `1124b523f`, 2026-11-02):

* A primitive `boolean` reads a JSON boolean, an integer token as set unless zero, and text after
  Java's `String.trim` as exactly `true`, `True`, `TRUE`, `false`, `False` or `FALSE`. Absence is the
  member's default, `false`. A JSON `null`, the empty or blank text and the text `null` reach Jackson's
  refusal of a null for a primitive and are unbindable, where kernel 30.8.1 read each as `false`. A number
  token with a fraction or an exponent is unbindable whatever its value, `1e0` and `0.0` included, while
  `-0` clears (2026-10-22 §1.2). Any other text and a container are unbindable.
* An `int` member reads text after `trim` through `Integer.parseInt`, whose digits are Java's BMP decimal
  digits, and a JSON number truncated toward zero when its value lies within the `int` range, in either
  spelling: `1e1` reads as `10.0` does (2026-10-22 §1.3). Absence is the member's own default. A primitive
  `int` (a group's count, a Number's fractional digits) is unbindable for every spelling that binds no
  value, as a primitive `boolean` is: JSON `null`, the empty or blank text and the text `null`. A boxed
  `Integer` (the base year, every length and the integer digits) reads those spellings as no value, as
  absence. Anything else that is no integer is unbindable on both.

Lean's JSON parser folds an exponent into the value, so `1e0` and `1` parse alike. The model-file
parser (`parseModelJson`) therefore first rewrites every exponent token as its plain decimal spelling
(`respellExponentTokens`), which keeps a fraction digit and with it the token's kind. The same pass refuses a
number token, and `decimalMember?` a bound text, of more than `modelNumberLengthLimit` characters, which
kernel 31.1.1's Jackson 3 refuses (a12-dmkits `ModelTextReadingDiffTest` at `1124b523f`, KF593). -/

namespace A12Kernel.Dm

open Lean A12Kernel

/-- The widest exponent `respellExponentTokens` writes out, as many zeros at most. A model carrying a wider one
is refused as outside the represented profile: how the Kernel binds such a member is unmeasured. -/
def modelNumberExponentBound : Nat := 100000

/-- The longest number token, or Number bound text, kernel 31.1.1 reads: 1000 characters, measured on a Number
bound (the text and the token of 1000 digits build, 1001 leave no model; a12-dmkits `ModelTextReadingDiffTest`
at `1124b523f`). That the limit holds for a number token anywhere else in the model is Jackson's one limit
applied everywhere, and is unmeasured beyond a bound. Whether the count is taken before or after Java's `trim`
for text is unmeasured too. -/
def modelNumberLengthLimit : Nat := 1000

/-- A strict JSON number token with an exponent, respelled in plain decimal with at least one fraction
digit (`1e0` as `1.0`, `1.5e-2` as `0.015`); `none` for every other token, which stays as written. -/
private def plainSpelling? (token : String) : Except String (Option String) :=
  let (negative, rest) := match token.toList with
    | '-' :: rest => (true, rest)
    | rest => (false, rest)
  let (integer, rest) := rest.span Char.isDigit
  let (fraction, rest) := match rest with
    | '.' :: rest => rest.span Char.isDigit
    | rest => ([], rest)
  let pointWritten := token.contains '.'
  match rest with
  | marker :: exponent =>
      let (exponentNegative, exponentDigits) := match exponent with
        | '-' :: digits => (true, digits)
        | '+' :: digits => (false, digits)
        | digits => (false, digits)
      if (marker != 'e' && marker != 'E') || integer.isEmpty || (integer.length > 1 && integer.head? == some '0') ||
          (pointWritten && fraction.isEmpty) || exponentDigits.isEmpty || !exponentDigits.all Char.isDigit then
        pure none
      else
        let significant := exponentDigits.dropWhile (· == '0')
        let magnitude := significant.foldl (fun value digit => value * 10 + (digit.toNat - '0'.toNat)) 0
        if significant.length > 6 || magnitude > modelNumberExponentBound then
          throw s!"model number {token} exceeds the represented exponent"
        else
          let shift : Int := magnitude
          let point : Int := integer.length + (if exponentNegative then -shift else shift)
          let digits := integer ++ fraction
          let (whole, part) :=
            if point ≤ 0 then (['0'], List.replicate point.natAbs '0' ++ digits)
            else if digits.length ≤ point.toNat then (digits ++ List.replicate (point.toNat - digits.length) '0', ['0'])
            else (digits.take point.toNat, digits.drop point.toNat)
          let whole := match whole.dropWhile (· == '0') with
            | [] => ['0']
            | kept => kept
          pure (some ((if negative then "-" else "") ++ String.ofList whole ++ "." ++ String.ofList part))
  | [] => pure none

private inductive ModelLexState where
  | plain | quoted | escaped | number

/-- A number token as the JSON parser should see it: refused when longer than `modelNumberLengthLimit`
characters, else respelled by `plainSpelling?`. -/
private def respelledToken (token : String) : Except String String := do
  if modelNumberLengthLimit < token.length then
    throw s!"model number token of {token.length} characters exceeds the reader's limit"
  pure ((← plainSpelling? token).getD token)

/-- Model text with each exponent token respelled by `plainSpelling?`, so it parses with a fraction as
its plain spelling does. Every other character, and every token that is no strict JSON number, passes
through for the JSON parser to judge, except that a token past `modelNumberLengthLimit` characters refuses
the model. -/
def respellExponentTokens (text : String) : Except String String := do
  let mut state := ModelLexState.plain
  let mut token := ""
  let mut output := ""
  for char in text.toList do
    match state with
    | .quoted =>
        output := output.push char
        if char == '\\' then state := .escaped
        else if char == '"' then state := .plain
    | .escaped =>
        output := output.push char
        state := .quoted
    | .plain =>
        if char.isDigit || char == '-' then
          token := String.singleton char
          state := .number
        else
          output := output.push char
          if char == '"' then state := .quoted
    | .number =>
        if char.isDigit || char == '.' || char == 'e' || char == 'E' || char == '+' || char == '-' then
          token := token.push char
        else
          output := output ++ (← respelledToken token)
          output := output.push char
          state := if char == '"' then .quoted else .plain
  if let .number := state then output := output ++ (← respelledToken token)
  pure output

/-- A text member that reads as no value: blank after `trim`, or the text `null`. -/
private def absentText (text : String) : Bool :=
  let trimmed := javaTrim text
  trimmed.isEmpty || trimmed == "null"

/-- A primitive `boolean` member; absence is `false`, the default of every measured member, and every
spelling that binds no value is unbindable. -/
def booleanMember? (json : Json) (key : String) : Except String Bool :=
  match json.getObjVal? key with
  | .error _ => pure false
  | .ok (.bool value) => pure value
  | .ok (.num number) =>
      if number.exponent == 0 then pure (number.mantissa != 0) else throw s!"{key} {number}"
  | .ok (.str text) =>
      match javaTrim text with
      | "true" | "True" | "TRUE" => pure true
      | "false" | "False" | "FALSE" => pure false
      | _ => throw s!"{key} {text}"
  | .ok other => throw s!"{key} {other.compress}"

/-- A temporal type's `youngerThan1900Check`: bound as a Boolean, so a spelling that binds no value still
leaves the model unread, but never checked or evaluated, so it reads as `false` whatever it says (kernel
31.3.1, A12K-4073; a12-dmkits KF677). -/
def inertYearCheck (body : Json) : Except String Bool := do
  let _ ← booleanMember? body "youngerThan1900Check"
  pure false

private def intMinimum : Int := -2147483648
private def intMaximum : Int := 2147483647

/-- `Integer.parseInt` over trimmed text: one optional sign, then Java's BMP decimal digits, inside the
`int` range. -/
private def parseJavaInt? (text : String) : Option Int := do
  let (negative, digits) := match text.toList with
    | '-' :: rest => (true, rest)
    | '+' :: rest => (false, rest)
    | rest => (false, rest)
  if digits.isEmpty then none
  let magnitude ← digits.foldlM (init := (0 : Nat)) fun value character =>
    (java21BmpDecimalDigitValue? character).map (value * 10 + ·)
  let value : Int := if negative then -(magnitude : Int) else magnitude
  if value < intMinimum || intMaximum < value then none else pure value

/-- A boxed `Integer` member: `none` for absence, `null`, a blank text and the text `null`. -/
def intMember? (json : Json) (key : String) : Except String (Option Int) :=
  match json.getObjVal? key with
  | .error _ | .ok .null => pure none
  | .ok (.num number) =>
      -- A fraction at least as long as the mantissa's digits is below one in magnitude and truncates
      -- to zero, which bounds the power below by the written digits.
      if (toString number.mantissa.natAbs).length ≤ number.exponent then pure (some 0) else
      -- The value is compared before truncation, so `2147483647.5` lies outside the range.
      let scale : Int := 10 ^ number.exponent
      if number.mantissa < intMinimum * scale || intMaximum * scale < number.mantissa then
        throw s!"{key} {number}"
      else pure (some (number.mantissa.tdiv scale))
  | .ok (.str text) =>
      if absentText text then pure none else
      match parseJavaInt? (javaTrim text) with
      | some value => pure (some value)
      | none => throw s!"{key} {text}"
  | .ok other => throw s!"{key} {other.compress}"

/-- A primitive `int` member: `none` for absence only. JSON `null`, a blank text and the text `null`, which
a boxed `Integer` reads as no value, leave no model here. -/
def primitiveIntMember? (json : Json) (key : String) : Except String (Option Int) :=
  match json.getObjVal? key with
  | .ok .null => throw s!"{key} null"
  | .ok (.str text) => if absentText text then throw s!"{key} {text}" else intMember? json key
  | _ => intMember? json key

/-- The primitive `boolean` members of a field type's body, by type name (every member the
2026-10-18 binding rows enumerate). -/
def fieldTypeBooleanMembers : String → List String
  | "StringType" => ["lineBreaksPermitted", "noValueValidation", "alphabeticalSorting"]
  | "NumberType" => ["zeroNotAllowed", "positivesOnly", "leadingZerosAllowed"]
  | "DateType" | "DateRangeType" | "DateFragmentType" => ["youngerThan1900Check"]
  | "EnumerationType" => ["alphabeticalSorting"]
  | _ => []

end A12Kernel.Dm
