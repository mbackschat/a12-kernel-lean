import Lean.Data.Json
import A12Kernel.Semantics.String
import A12Kernel.Elaboration.DeclarationAdmission

/-! # How the Kernel's DM-JSON binding reads a member that is not text

The Kernel deserializes a model into Java objects before any consistency check, so a member it cannot
bind leaves no model at all: that is a read failure here, never a Kernel class. Two laws cover every
non-text member measured, on every carrier the a12-dmkits handbacks of 2026-10-18 and 2026-10-21 name
(`docs/sources/inbound-handbacks.md#src-inbound-2026-10-18`, `#src-inbound-2026-10-21`):

* A primitive `boolean` reads a JSON boolean, an integer as set unless zero, and text after Java's
  `String.trim` as exactly `true`, `True`, `TRUE`, `false`, `False` or `FALSE`. The empty text and the
  text `null` are the member's default, as JSON `null` and absence are. A number written with a
  fraction, any other text and a container are unbindable.
* An `int` member, a group count or the base year, reads text after `trim` through `Integer.parseInt`,
  whose digits are Java's BMP decimal digits, and a JSON number truncated toward zero when its value
  lies within the `int` range. The empty text and the text `null` are no value. Anything else is
  unbindable.

Lean's JSON reader keeps a number's value, not its spelling, so `1e0` reads as the integer `1` while
the peer reports it unbindable on a boolean; no Kernel row measures that spelling. -/

namespace A12Kernel.Dm

open Lean A12Kernel

/-- A text member that reads as no value: blank after `trim`, or the text `null`. -/
private def absentText (text : String) : Bool :=
  let trimmed := javaTrim text
  trimmed.isEmpty || trimmed == "null"

/-- A primitive `boolean` member; absent and every default spelling are `false`, the default of every
measured member. -/
def booleanMember? (json : Json) (key : String) : Except String Bool :=
  match json.getObjVal? key with
  | .error _ | .ok .null => pure false
  | .ok (.bool value) => pure value
  | .ok (.num number) =>
      if number.exponent == 0 then pure (number.mantissa != 0) else throw s!"{key} {number}"
  | .ok (.str text) =>
      if absentText text then pure false else
      match javaTrim text with
      | "true" | "True" | "TRUE" => pure true
      | "false" | "False" | "FALSE" => pure false
      | _ => throw s!"{key} {text}"
  | .ok other => throw s!"{key} {other.compress}"

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

/-- An `int` member: `none` for absent, `null`, a blank text and the text `null`. -/
def intMember? (json : Json) (key : String) : Except String (Option Int) :=
  match json.getObjVal? key with
  | .error _ | .ok .null => pure none
  | .ok (.num number) =>
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

/-- The primitive `boolean` members of a field type's body, by type name (every member the
2026-10-18 binding rows enumerate). -/
def fieldTypeBooleanMembers : String → List String
  | "StringType" => ["lineBreaksPermitted", "noValueValidation", "alphabeticalSorting"]
  | "NumberType" => ["zeroNotAllowed", "positivesOnly", "leadingZerosAllowed"]
  | "DateType" | "DateRangeType" | "DateFragmentType" => ["youngerThan1900Check"]
  | "EnumerationType" => ["alphabeticalSorting"]
  | _ => []

/-- The first boolean member of a field type that does not bind. Only the body its `type` names is
bound: another type's object beside it is never read (2026-10-21 §1.3). -/
def fieldTypeBindingRefusal? (fieldType : Json) : Option String := do
  let typeName ← (fieldType.getObjValAs? String "type").toOption
  let body ← (fieldType.getObjVal? typeName).toOption
  (fieldTypeBooleanMembers typeName).findSome? fun key =>
    match booleanMember? body key with
    | .error reason => some reason
    | .ok _ => none

/-- The first member of a field element that does not bind: its own flags, then its type's. -/
def fieldBindingRefusal? (fieldJson : Json) : Option String :=
  (["global", "transient"].findSome? fun key =>
    match booleanMember? fieldJson key with
    | .error reason => some reason
    | .ok _ => none).orElse fun _ =>
    (fieldJson.getObjVal? "fieldType").toOption.bind fieldTypeBindingRefusal?

end A12Kernel.Dm
