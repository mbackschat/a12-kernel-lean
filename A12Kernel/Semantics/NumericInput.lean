import A12Kernel.Semantics.NumericTarget
import A12Kernel.Semantics.Observation
import A12Kernel.Semantics.String

/-! # Stored Number input and formal-read selection

This capsule owns the representation boundary between a Number cell's stored value and the one text consumed by formal checking and value-reading operators. A decimal-valued placement retains its exact signed scale and derives a stripped/minimum-scale read; a String-valued placement remains verbatim. Host ingestion, locale-specific separators, semantic-index normalization, and computed-target rendering remain separate.
-/

namespace A12Kernel

/-- Exact decimal-valued source identity, including the negative scales that plain rendering erases. -/
structure NumericInputDecimal where
  unscaled : Int
  scale : Int
  deriving Repr, DecidableEq

namespace NumericInputDecimal

/-- Plain dot-decimal storage text. Negative scale is expanded without losing the retained identity. -/
def storedNumber (value : NumericInputDecimal) : StoredNumber :=
  if value.scale < 0 then
    { unscaled := value.unscaled * (decimalFactor value.scale.natAbs : Nat)
      scale := 0 }
  else
    { unscaled := value.unscaled
      scale := value.scale.toNat }

/-- Render the exact decimal as the plain text physically retained by the document. -/
def storedText (value : NumericInputDecimal) : String :=
  value.storedNumber.render

/-- The computed-target equality quotient. A negative-scale source cannot equal canonical computed output even when its plain text agrees. -/
def sourceIdentity (value : NumericInputDecimal) : NumericSourceIdentity :=
  if value.scale < 0 then
    .nonComputedForm
  else
    .decimal { unscaled := value.unscaled, scale := value.scale.toNat }

/-- Strip only fractional trailing zeros and then pad to the declaration's minimum fractional scale. -/
def formalReadStored (value : NumericInputDecimal)
    (minimumScale : Nat) : StoredNumber :=
  let stored := value.storedNumber
  let (magnitude, naturalScale) :=
    StoredNumber.stripFractionalZeros stored.unscaled.natAbs stored.scale
  let selectedScale := max naturalScale minimumScale
  let selectedMagnitude :=
    magnitude * decimalFactor (selectedScale - naturalScale)
  { unscaled :=
      if stored.unscaled < 0 then -(selectedMagnitude : Int)
      else selectedMagnitude
    scale := selectedScale }

/-- Render the declaration-adjusted text consumed by formal checking and value readers. -/
def formalReadText (value : NumericInputDecimal)
    (minimumScale : Nat) : String :=
  (value.formalReadStored minimumScale).render

end NumericInputDecimal

/-- The two in-memory Number storage regimes. Empty placements are represented outside this type. -/
inductive NumericStoredInput where
  | decimal (value : NumericInputDecimal)
  | text (value : String)
  deriving Repr, DecidableEq

namespace NumericStoredInput

/-- Embed the existing nonnegative-scale stored decimal identity into the input regime. -/
def ofStoredNumber (value : StoredNumber) : NumericStoredInput :=
  .decimal { unscaled := value.unscaled, scale := value.scale }

/-- The exact physical storage text selected by the input regime. -/
def storedText : NumericStoredInput → String
  | .decimal value => value.storedText
  | .text value => value

/-- Select the one text observed by every runtime evaluation channel. -/
def formalReadText (minimumScale : Nat) : NumericStoredInput → String
  | .decimal value => value.formalReadText minimumScale
  | .text value => value

/-- The scale-sensitive identity used when comparing original and computed target storage. -/
def sourceIdentity : NumericStoredInput → NumericSourceIdentity
  | .decimal value => value.sourceIdentity
  | .text _ => .nonComputedForm

end NumericStoredInput

/-- First-failure classes needed to separate Number formal-read behavior. Public messages remain a later boundary. -/
inductive NumericFormalReadError where
  | malformed
  | totalDigitsTooLong
  | signedZero
  | negativeNotAllowed
  | decimalSeparatorForbidden
  | decimalSeparatorRequired
  | fractionalDigitsOutOfRange
  | integerDigitsTooLong
  | zeroNotAllowed
  | leadingZerosNotAllowed
  | textTooShort
  | textTooLong
  | belowMinimum
  | aboveMaximum
  deriving Repr, DecidableEq

/-- Parsed ASCII dot-decimal text together with lexical facts that exact rational value alone erases. -/
structure ParsedNumericFormalRead where
  value : Rat
  negative : Bool
  hasDecimalSeparator : Bool
  fractionalDigits : Nat
  integerDigits : Nat
  digitCount : Nat
  leadingZeros : Bool
  deriving Repr, DecidableEq

/-- Parse the Number formal check's locale-neutral dot-decimal profile: optional minus, nonempty ASCII integer digits, and an optional dot followed by nonempty ASCII fractional digits. -/
def parseNumericFormalRead? (text : String) : Option ParsedNumericFormalRead := do
  let (negative, characters) := match text.toList with
    | '-' :: rest => (true, rest)
    | rest => (false, rest)
  let (wholeCharacters, suffix) := characters.span (· != '.')
  if wholeCharacters.isEmpty then none else
  let whole ← parseAsciiNatural? (String.ofList wholeCharacters)
  let (fraction, fractionalDigits, hasDecimalSeparator) ← match suffix with
    | [] => some (0, 0, false)
    | '.' :: fractionCharacters =>
        if fractionCharacters.isEmpty then none else
        let fraction ← parseAsciiNatural? (String.ofList fractionCharacters)
        some (fraction, fractionCharacters.length, true)
    | _ => none
  let factor := decimalFactor fractionalDigits
  let magnitude : Rat := whole + (fraction : Rat) / factor
  some {
    value := if negative then -magnitude else magnitude
    negative
    hasDecimalSeparator
    fractionalDigits
    integerDigits := wholeCharacters.length
    digitCount := wholeCharacters.length + fractionalDigits
    leadingZeros := wholeCharacters.length > 1 &&
      wholeCharacters.head? == some '0' }

namespace NumericTargetConstraints

/-- Return the first Number formal-read failure after storage-regime selection. The order follows the ordinary basic check; locale/presentation conversion has already happened. -/
def firstFormalReadError? (constraints : NumericTargetConstraints)
    (info : NumField) (text : String)
    (parsed : ParsedNumericFormalRead) : Option NumericFormalReadError :=
  if numericStoredDigitLimit < parsed.digitCount then
    some .totalDigitsTooLong
  else if parsed.negative && parsed.value = 0 &&
      constraints.zeroAllowed && info.signed then
    some .signedZero
  else if parsed.negative && !info.signed then
    some .negativeNotAllowed
  else if info.scale = 0 && parsed.hasDecimalSeparator then
    some .decimalSeparatorForbidden
  else if 0 < constraints.minFractionalDigits &&
      !parsed.hasDecimalSeparator then
    some .decimalSeparatorRequired
  else if parsed.fractionalDigits < constraints.minFractionalDigits ||
      info.scale < parsed.fractionalDigits then
    some .fractionalDigitsOutOfRange
  else if constraints.maxIntegerDigits.any
      (fun maximum => maximum < parsed.integerDigits) then
    some .integerDigitsTooLong
  else if parsed.value = 0 && !constraints.zeroAllowed then
    some .zeroNotAllowed
  else if parsed.leadingZeros && !constraints.leadingZerosAllowed then
    some .leadingZerosNotAllowed
  else if constraints.minStoredLength.any
      (fun minimum => text.length < minimum) then
    some .textTooShort
  else if constraints.maxStoredLength.any
      (fun maximum => maximum < text.length) then
    some .textTooLong
  else if constraints.minimum.any (fun minimum => parsed.value < minimum) then
    some .belowMinimum
  else if constraints.maximum.any (fun maximum => maximum < parsed.value) then
    some .aboveMaximum
  else
    none

/-- Select the storage-regime text and run the declaration-owned Number check. -/
def checkFormalRead (constraints : NumericTargetConstraints)
    (info : NumField) (input : NumericStoredInput) :
    Except NumericFormalReadError (String × Rat) :=
  let text := input.formalReadText constraints.minFractionalDigits
  match parseNumericFormalRead? text with
  | none => .error .malformed
  | some parsed =>
      match constraints.firstFormalReadError? info text parsed with
      | some error => .error error
      | none => .ok (text, parsed.value)

/-- Project one selected input into the established scalar parser boundary. Detailed Number errors remain available from `checkFormalRead`; the shared checked cell retains the existing coarse formal cause. -/
def classifyFormalRead (constraints : NumericTargetConstraints)
    (info : NumField) (input : NumericStoredInput) : RawCell Value :=
  match constraints.checkFormalRead info input with
  | .ok (_, value) => .parsed (.num value)
  | .error .malformed => .rejected .malformed
  | .error _ => .rejected .declaredConstraint

end NumericTargetConstraints

end A12Kernel
