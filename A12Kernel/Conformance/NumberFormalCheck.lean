import A12Kernel.Semantics.NumberFormalCheck

/-! # Ordered Number formal-check locks

These cases lock the *order* of the runtime Number formal cascade, not merely its individual tests: every case below is a value that fails at least two declared constraints, so it separates this account from one that reports a different failing constraint. The declarations mirror the probe model behind `docs/sources/evaluation-and-application-routes.md`.

The four lexical refusals named in the semantics module are deliberately absent: a document-loaded value reaches this clause already canonical, so no input in this domain can carry a plus sign, a redundant minus on zero, a leading zero, or a missing separator.
-/

namespace A12Kernel.Conformance.NumberFormalCheck

open A12Kernel

/-- `ZPlain` — an integer-only plain Number with no other constraint. -/
private def plain : NumberFormalDeclaration :=
  { maxFractionalDigits := some 0 }

/-- `MC` — the money declaration whose four constraints let a single value choose between them. -/
private def money : NumberFormalDeclaration := {
  minFractionalDigits := 2
  maxFractionalDigits := some 2
  maxIntegerDigits := some 4
  minLength := some 4
  maxLength := some 8
  minValue := some { unscaled := 1, scale := 0 }
  maxValue := some { unscaled := 5000, scale := 0 }
  zeroNotAllowed := true
  amount := true
}

/-- `ZNoZero` — the only probed shape whose length pair can decide, since a declaration with
fractional places renders at least four characters and one with a digit ceiling refuses first. -/
private def noZero : NumberFormalDeclaration := {
  maxFractionalDigits := some 0
  minLength := some 2
  maxLength := some 4
  zeroNotAllowed := true
}

/-- `Capped` — bounds without a digit ceiling, the only shape that lets a bound win. -/
private def capped : NumberFormalDeclaration := {
  maxFractionalDigits := some 0
  minValue := some { unscaled := 10, scale := 0 }
  maxValue := some { unscaled := 20, scale := 0 }
}

private def num (unscaled : Int) (scale : Nat) : NumberFormalInput :=
  .value { unscaled, scale }

/- Text the loader cannot read as a number refuses before every declared constraint is consulted. -/
example :
    numberFormalCheck money .unreadable = some .unreadable ∧
      numberFormalCheck plain .unreadable = some .unreadable := by
  native_decide

/- The universal fifteen-digit ceiling outranks every declaration-specific test: this value also
   exceeds `money`'s four integer digits, its eight-character length, and its maximum. -/
example :
    numberFormalCheck money (num 1234567890123456 0) = some .tooManyDigits ∧
      numberFormalCheck plain (num 1234567890123456 0) = some .tooManyDigits := by
  native_decide

/- A positives-only declaration refuses the sign ahead of the bound the same value also violates. -/
example :
    numberFormalCheck { capped with positivesOnly := true } (num (-5) 0) =
        some .signedValue ∧
      numberFormalCheck capped (num (-5) 0) = some .belowMinimum := by
  native_decide

/- A separator is refused outright only when no fractional place is declared; `money` instead reads
   the same value's fractional digit count. -/
example :
    numberFormalCheck plain (num 15 1) = some .separatorNotAllowed ∧
      numberFormalCheck money (num 51234 4) = some .fractionalDigitCount := by
  native_decide

/- The declared fractional range is a range: its interior is admitted, both ends included. -/
example :
    numberFormalCheck { minFractionalDigits := 1, maxFractionalDigits := some 3 }
        (num 12345 3) = none ∧
      numberFormalCheck { minFractionalDigits := 1, maxFractionalDigits := some 3 }
        (num 51234 4) = some .fractionalDigitCount := by
  native_decide

/- The integer-digit ceiling is consulted before both bounds, which is why no probe value ever
   reported a maximum violation on a declaration that also caps digits: `99999.00` exceeds `money`'s
   maximum of 5000 as well, and the digit ceiling is what it reports. -/
example :
    numberFormalCheck money (num 9999900 2) = some .tooManyIntegerDigits ∧
      numberFormalCheck capped (num 25 0) = some .aboveMaximum := by
  native_decide

/- Loading is what makes zero reachable on a money declaration: the stored `0` arrives at the
   declared scale, clears the fractional test, and only then meets the zero refusal. -/
example :
    numberFormalCheck money (num 0 2) = some .zeroNotAllowed ∧
      numberFormalCheck money (num 0 0) = some .fractionalDigitCount := by
  native_decide

/- Length counts the rendered text rather than the digits, so the same magnitude passes the minimum
   once it carries a sign. A declaration with fractional places can never be too short, which is why
   only the integer shape locks this pair. -/
example :
    numberFormalCheck noZero (num 5 0) = some .tooShort ∧
      numberFormalCheck noZero (num (-5) 0) = none ∧
      numberFormalCheck noZero (num 123456 0) = some .tooLong := by
  native_decide

/- A value inside every declared constraint is admitted. -/
example :
    numberFormalCheck money (num 150000 2) = none ∧
      numberFormalCheck capped (num 15 0) = none ∧
      numberFormalCheck plain (num 123456 0) = none := by
  native_decide

/- Each refusal carries the code a `validateFull` consumer reads; the code is a function of the
   failing test alone, never of the money trait that selects the message text. -/
example :
    (numberFormalCheck money (num 9999900 2)).map NumberFormalRefusal.errorCode =
        some "zahlZuvieleVorkommastellen" ∧
      (numberFormalCheck { money with amount := false } (num 9999900 2)).map
          NumberFormalRefusal.errorCode = some "zahlZuvieleVorkommastellen" := by
  native_decide

end A12Kernel.Conformance.NumberFormalCheck
