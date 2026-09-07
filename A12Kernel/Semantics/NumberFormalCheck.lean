import A12Kernel.Semantics.NumericStoredNumber

/-! # The runtime Number formal-check cascade

A Number cell's declared constraints are not checked as a set that yields a set of failures. The
Kernel consults them in a fixed order and returns the **first** one that fails, so the refusal a
consumer observes is a function of that order and not merely of which constraints the value violates.
This capsule owns that order and the surfaced code each step produces.

Two independent axes meet here and are easy to conflate. The surfaced **code** is chosen by the
failing test alone. The rendered message **text** is chosen by the failing test *together with* the
number's art — plain, money-with-cents, or money-without-cents — so one code stands behind up to
three texts. Only the code is modelled here; the text refinement belongs to message rendering.

**Input domain.** This clause consumes a value that has already been loaded into a document, which is
where the Kernel canonicalises it: fractional trailing zeros are stripped and the result is padded
back up to the declared minimum scale — the same projection `NumericInput` already owns for the
decimal-valued formal read. That is why `5.00` on an integer declaration reports a bound violation
rather than a stray separator, and why `0` on a two-place money declaration reaches the zero refusal
instead of the fractional-count one.

Four refusals in the Kernel's own catalog test the *lexical* shape
that canonicalisation removes — a leading plus (`zahlMitPlus`), a signed zero
(`zahlNullEnthaeltVorzeichen`), a leading zero (`zahlHatFuehrendeNullen`), and an absent separator
where fractional places are declared (`zahlOhneDezimalTrenner`). They are absent from
`NumberFormalRefusal` because no value in this domain can exhibit their conditions, not because the
Kernel lacks them: they belong to the display-to-internal conversion entry point, whose input is raw
text. `docs/SEMANTICS-GAPS.md` carries that route as an open obligation.
-/

namespace A12Kernel

/-- The declared Number constraints the runtime formal check consults, named for what they bound
rather than for the Kernel's internal field names. `maxFractionalDigits := none` means the
declaration left the fractional scale open; `minFractionalDigits := 0` is the absent minimum, since
zero fractional places is also the plain-integer declaration. -/
structure NumberFormalDeclaration where
  minFractionalDigits : Nat := 0
  maxFractionalDigits : Option Nat := none
  maxIntegerDigits : Option Nat := none
  minLength : Option Nat := none
  maxLength : Option Nat := none
  minValue : Option StoredNumber := none
  maxValue : Option StoredNumber := none
  zeroNotAllowed : Bool := false
  /-- The Kernel's `positivesOnly`, whose default is `false` — a Number is signed unless declared
  otherwise, which is why an unannotated declaration admits a negative value. -/
  positivesOnly : Bool := false
  /-- The money trait. It selects the message text, never the surfaced code. -/
  amount : Bool := false
  deriving Repr, DecidableEq

/-- A document-loaded Number cell as the formal check receives it: either the loader could not read a
number from the stored text at all, or it produced an exact decimal. -/
inductive NumberFormalInput where
  | unreadable
  | value (stored : StoredNumber)
  deriving Repr, DecidableEq

/-- The refusals reachable from a document-loaded value, one per surfaced code. -/
inductive NumberFormalRefusal where
  | unreadable
  | tooManyDigits
  | signedValue
  | separatorNotAllowed
  | fractionalDigitCount
  | tooManyIntegerDigits
  | zeroNotAllowed
  | tooShort
  | tooLong
  | belowMinimum
  | aboveMaximum
  deriving Repr, DecidableEq

namespace NumberFormalRefusal

/-- The code a `validateFull` consumer reads. It is determined by the failing test alone: the same
refusal on a money declaration and on a plain one carries this same code and differs only in the
rendered text. -/
def errorCode : NumberFormalRefusal → String
  | .unreadable => "zahlHatUngueltigeZeichen"
  | .tooManyDigits => "stelligkeitZuLang"
  | .signedValue => "zahlMitVorzeichen"
  | .separatorNotAllowed => "zahlHatDezimalTrenner"
  | .fractionalDigitCount => "zahlFalscheAnzahlNachkommastellen"
  | .tooManyIntegerDigits => "zahlZuvieleVorkommastellen"
  | .zeroNotAllowed => "zahlIstNull"
  | .tooShort => "zahlZuKurz"
  | .tooLong => "zahlZuLang"
  | .belowMinimum => "zahlZuKlein"
  | .aboveMaximum => "zahlZuGross"

end NumberFormalRefusal

/-- The universal stored-digit ceiling, applied before every declaration-specific test and counting
neither the sign nor the separator. -/
def numberFormalDigitCeiling : Nat := 15

/-- Whether the value's fractional scale satisfies the declared fractional range.

The three cases are the Kernel's own, and they are not a single interval test: an open maximum
demands the minimum *exactly*, so a declaration of two fractional places with no maximum admits
`1.50` and refuses `1.5000`, while the same minimum with a maximum of four admits both. -/
def numberFractionalScaleAdmitted (declaration : NumberFormalDeclaration) (scale : Nat) : Bool :=
  match declaration.maxFractionalDigits with
  | none => declaration.minFractionalDigits == 0 || scale == declaration.minFractionalDigits
  | some maximum => declaration.minFractionalDigits ≤ scale && scale ≤ maximum

/-- The ordered cascade. Each guard is the Kernel's, in the Kernel's order; the first that fails
decides the refusal, and a value reaching the end is admitted.

The order is load-bearing rather than incidental. A value that overflows both the integer-digit
ceiling and the declared maximum reports the digit ceiling, so an account that checked bounds first
would name a different constraint for the same input — which is what the conformance locks separate.
-/
def numberFormalCheck (declaration : NumberFormalDeclaration) :
    NumberFormalInput → Option NumberFormalRefusal
  | .unreadable => some .unreadable
  | .value stored =>
      if stored.digitCount > numberFormalDigitCeiling then
        some .tooManyDigits
      else if declaration.positivesOnly && stored.unscaled < 0 then
        some .signedValue
      else if declaration.minFractionalDigits == 0 &&
          (declaration.maxFractionalDigits.getD 0 == 0) && stored.scale > 0 then
        some .separatorNotAllowed
      else if !numberFractionalScaleAdmitted declaration stored.scale then
        some .fractionalDigitCount
      else if declaration.maxIntegerDigits.any (stored.integerDigitCount > ·) then
        some .tooManyIntegerDigits
      else if declaration.zeroNotAllowed && stored.unscaled == 0 then
        some .zeroNotAllowed
      else if declaration.minLength.any (stored.render.length < ·) then
        some .tooShort
      else if declaration.maxLength.any (stored.render.length > ·) then
        some .tooLong
      else if declaration.minValue.any (stored.amount < ·.amount) then
        some .belowMinimum
      else if declaration.maxValue.any (stored.amount > ·.amount) then
        some .aboveMaximum
      else
        none

end A12Kernel
