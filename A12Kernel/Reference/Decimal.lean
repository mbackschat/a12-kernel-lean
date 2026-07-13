import Init.Data.Rat

/-! # Canonical finite-decimal parsing

The public reference protocol transports exact decimal numbers as strings. This module admits one canonical spelling for each supported finite decimal and constructs a `Rat` without passing through floating-point arithmetic.
-/

namespace A12Kernel.Reference.Decimal

/-- Maximum number of characters admitted by the decimal transport boundary. -/
def maxCharacters : Nat := 256

/-- A stable classification of decimal transport failures. -/
inductive Error where
  /-- The input crossed the transport's resource bound before parsing began. -/
  | tooLong
  /-- The input is not the unique admitted spelling of a finite decimal. -/
  | invalidCanonical
  deriving Repr, DecidableEq

private def asciiDigit? (character : Char) : Option Nat :=
  let code := character.toNat
  if '0'.toNat ≤ code ∧ code ≤ '9'.toNat then
    some (code - '0'.toNat)
  else
    none

private def accumulateDigits : List Char → Nat → Option Nat
  | [], value => some value
  | character :: rest, value =>
      match asciiDigit? character with
      | some digit => accumulateDigits rest (value * 10 + digit)
      | none => none

private def wholeValue? : List Char → Option Nat
  | ['0'] => some 0
  | [] => none
  | '0' :: _ => none
  | first :: rest => do
      let digit ← asciiDigit? first
      accumulateDigits rest digit

private def fractionalValue? (characters : List Char) : Option (Nat × Nat) := do
  if characters.isEmpty ∨ characters.getLast? == some '0' then
    none
  else
    let value ← accumulateDigits characters 0
    some (value, characters.length)

private def exactValue (negative : Bool) (whole fractionDigits fractionValue : Nat) : Rat :=
  let denominator := 10 ^ fractionDigits
  let magnitude := whole * denominator + fractionValue
  let numerator : Int := if negative then -(magnitude : Int) else magnitude
  Rat.normalize numerator denominator (Nat.ne_of_gt <| Nat.pow_pos (by decide))

private def parseMagnitude (negative : Bool) (characters : List Char) : Except Error Rat := do
  let (wholeCharacters, remainder) := characters.span (fun character => character != '.')
  let some whole := wholeValue? wholeCharacters
    | .error .invalidCanonical
  match remainder with
  | [] =>
      if negative && whole == 0 then
        .error .invalidCanonical
      else
        .ok (exactValue negative whole 0 0)
  | '.' :: fractionalCharacters =>
      let some (fractionalValue, fractionalDigits) := fractionalValue? fractionalCharacters
        | .error .invalidCanonical
      .ok (exactValue negative whole fractionalDigits fractionalValue)
  | _ => .error .invalidCanonical

/-- Parse a canonical finite decimal directly into an exact rational number. -/
def parse (input : String) : Except Error Rat :=
  if input.length > maxCharacters then
    .error .tooLong
  else
    match input.toList with
    | '-' :: magnitude => parseMagnitude true magnitude
    | magnitude => parseMagnitude false magnitude

private def isInvalidCanonical : Except Error Rat → Bool
  | .error .invalidCanonical => true
  | .error .tooLong | .ok _ => false

private def value? : Except Error Rat → Option Rat
  | .ok value => some value
  | .error _ => none

private def error? : Except Error Rat → Option Error
  | .error error => some error
  | .ok _ => none

example : value? (parse "0") = some 0 := by
  native_decide

example : value? (parse "42") = some (42 : Rat) := by
  native_decide

example : value? (parse "-7") = some (-7 : Rat) := by
  native_decide

example : value? (parse "-0.5") = some (-(1 / 2 : Rat)) := by
  native_decide

example : value? (parse "12.34") = some (617 / 50 : Rat) := by
  native_decide

example : value? (parse "0.005") = some (1 / 200 : Rat) := by
  native_decide

example :
    ["", "+", "+1", "-", "1e2", "1E2", "-0", "01", "-01", "1.0", "1.20", "1.",
      ".5", "1.2.3", " 1"].all (isInvalidCanonical ∘ parse) := by
  native_decide

example :
    (value? (parse (String.ofList (List.replicate maxCharacters '1')))).isSome = true := by
  native_decide

example : error? (parse (String.ofList (List.replicate (maxCharacters + 1) '1'))) =
    some .tooLong := by
  native_decide

end A12Kernel.Reference.Decimal
