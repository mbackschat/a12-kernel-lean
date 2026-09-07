import A12Kernel.Semantics.RuntimeFormalMessageKey

/-! # Runtime formal message-key locks

These cases lock the two things the key vocabulary is for: that a refusal's **key** varies with the
declaration where its **code** does not, and that each key's parameter contract is what a consumer
must supply. They deliberately assert nothing about rendered text, which this project does not carry.
-/

namespace A12Kernel.Conformance.RuntimeFormalMessageKey

open A12Kernel

private def plain : NumberFormalDeclaration :=
  { maxFractionalDigits := some 0 }

private def withCents : NumberFormalDeclaration :=
  { amount := true, minFractionalDigits := 2, maxFractionalDigits := some 2 }

private def withoutCents : NumberFormalDeclaration :=
  { amount := true, minFractionalDigits := 0, maxFractionalDigits := some 0 }

/- The art is read from the declaration, and the with-cents family is selected at exactly two
   fractional places — one and three fall to the without-cents family despite also carrying cents. -/
example :
    plain.art = .plain ∧
      withCents.art = .moneyWithCents ∧
      withoutCents.art = .moneyWithoutCents ∧
      { amount := true, minFractionalDigits := 1 : NumberFormalDeclaration }.art =
        .moneyWithoutCents ∧
      { amount := true, minFractionalDigits := 3 : NumberFormalDeclaration }.art =
        .moneyWithoutCents := by
  native_decide

/- One refusal, one code, three keys. This is the pairing the whole capsule exists to separate: an
   implementation deriving its code from the message key would report three distinct codes here. -/
example :
    (numberMessageKey plain .tooLong).bundleKey = "ZAHL_ZU_LANG" ∧
      (numberMessageKey withCents .tooLong).bundleKey = "GBMC_ZU_LANG" ∧
      (numberMessageKey withoutCents .tooLong).bundleKey = "GBOC_ZU_LANG" ∧
      NumberFormalRefusal.tooLong.errorCode = "zahlZuLang" := by
  native_decide

/- The sign splits the key on the unreadable and fractional-count refusals, so one refusal on one art
   still has two keys — and the code stays single. -/
example :
    (numberMessageKey { withCents with positivesOnly := false } .unreadable).bundleKey =
        "GBMC_MIT_UNGUELTIGEN_ZEICHEN_MVZ" ∧
      (numberMessageKey { withCents with positivesOnly := true } .unreadable).bundleKey =
        "GBMC_MIT_UNGUELTIGEN_ZEICHEN_OVZ" ∧
      NumberFormalRefusal.unreadable.errorCode = "zahlHatUngueltigeZeichen" := by
  native_decide

/- The zero refusal leaves its own family: on both money arts it selects the plain keys, which is the
   single place the three families are not parallel. -/
example :
    (numberMessageKey withCents .zeroNotAllowed).bundleKey = "ZAHL_IST_NULL" ∧
      (numberMessageKey withoutCents .zeroNotAllowed).bundleKey = "ZAHL_IST_NULL" ∧
      (numberMessageKey { withCents with positivesOnly := true } .zeroNotAllowed).bundleKey =
        "ZAHL_IST_NULL_OVZ" := by
  native_decide

/- The universal digit ceiling is art-independent, unlike every other refusal above. -/
example :
    [plain, withCents, withoutCents].map (fun d => (numberMessageKey d .tooManyDigits).bundleKey) =
      List.replicate 3 "STELLIGKEIT_ZU_LANG" := by
  native_decide

/- The parameter contract is what a consumer must supply, and it is not uniform within a family: the
   two length refusals interpolate different bounds, and the zero refusal interpolates nothing. -/
example :
    (RuntimeFormalMessageKey.textZahlZuLang).parameters = [.maxLength] ∧
      (RuntimeFormalMessageKey.textZahlZuKurz).parameters = [.minLength] ∧
      (RuntimeFormalMessageKey.textZahlIstNull).parameters = [] ∧
      (RuntimeFormalMessageKey.textZahlZuKlein).parameters = [.minValue] ∧
      (RuntimeFormalMessageKey.textZahlZuGross).parameters = [.maxValue] := by
  native_decide

/- A key's descriptor pairs its Kernel name with its parameters, so the two cannot drift apart. -/
example :
    RuntimeFormalMessageKey.textStelligkeitZuLang.descriptor = ("STELLIGKEIT_ZU_LANG", []) := by
  native_decide

end A12Kernel.Conformance.RuntimeFormalMessageKey
