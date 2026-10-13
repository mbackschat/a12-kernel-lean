import A12Kernel.Semantics.RuntimeFormalMessageKey

/-! # Runtime formal message-key locks

These cases lock the two things the key vocabulary is for: that a refusal's **key** varies with the
declaration where its **code** does not, and that each key's parameter contract is what a consumer
must supply. They deliberately assert nothing about rendered text, which this project does not carry.
-/

namespace A12Kernel.Conformance.RuntimeFormalMessageKey

open A12Kernel

private def integer : NumField := { scale := 0, signed := true }
private def twoPlaces : NumField := { scale := 2, signed := true }

private def key (constraints : NumericTargetConstraints) (info : NumField)
    (error : NumericFormalReadError) : String :=
  (numberMessageKey constraints info error).bundleKey

/- The with-cents family is selected at exactly two minimum fractional places; one and three fall to
   the without-cents family, which is what the K16 money row separates by rendered text. -/
example :
    ({} : NumericTargetConstraints).art = .plain ∧
      ({ amount := true, minFractionalDigits := 2 } : NumericTargetConstraints).art = .moneyWithCents ∧
      [1, 3].all (fun places =>
        ({ amount := true, minFractionalDigits := places } : NumericTargetConstraints).art ==
          .moneyWithoutCents) := by
  native_decide

/- One refusal, one code, three keys: an implementation deriving its code from the key would report
   three codes here. -/
example :
    key {} integer .textTooLong = "ZAHL_ZU_LANG" ∧
      key { amount := true, minFractionalDigits := 2 } twoPlaces .textTooLong = "GBMC_ZU_LANG" ∧
      key { amount := true } integer .textTooLong = "GBOC_ZU_LANG" ∧
      NumericFormalReadError.textTooLong.errorCode = "zahlZuLang" := by
  native_decide

/- On a plain Number the unreadable-text, missing-separator and fractional-count refusals share a key
   split by fractional shape, and only the fixed shape reads the sign. The integer and variable arms
   are the K16 scale-0 and scale-2 rows. -/
example :
    key {} integer .malformed = "ZAHL_MIT_UNGUELTIGEN_ZEICHEN_ONK" ∧
      key {} twoPlaces .malformed = "ZAHL_MIT_UNGUELTIGEN_ZEICHEN_VNK" ∧
      key { minFractionalDigits := 2 } twoPlaces .decimalSeparatorRequired =
        "ZAHL_MIT_UNGUELTIGEN_ZEICHEN_FNKPVZ" ∧
      key { minFractionalDigits := 2 } { twoPlaces with signed := false } .fractionalDigitsOutOfRange =
        "ZAHL_MIT_UNGUELTIGEN_ZEICHEN_FNKOVZ" ∧
      key { minFractionalDigits := 1 } twoPlaces .fractionalDigitsOutOfRange =
        "ZAHL_MIT_UNGUELTIGEN_ZEICHEN_VNK" := by
  native_decide

/- On a money Number the same three refusals split by sign instead, and the separator refusal joins
   them on the without-cents family rather than keeping its plain key. -/
example :
    key { amount := true, minFractionalDigits := 2 } twoPlaces .fractionalDigitsOutOfRange =
        "GBMC_MIT_UNGUELTIGEN_ZEICHEN_MVZ" ∧
      key { amount := true, minFractionalDigits := 1 } { scale := 1, signed := false } .malformed =
        "GBOC_MIT_UNGUELTIGEN_ZEICHEN_OVZ" ∧
      key { amount := true } integer .decimalSeparatorForbidden = "GBOC_MIT_UNGUELTIGEN_ZEICHEN_MVZ" ∧
      key {} integer .decimalSeparatorForbidden = "ZAHL_HAT_DEZIMALTRENNER" := by
  native_decide

/- The plus refusal selects the plus key only on a signed declaration; an unsigned one reports the
   sign key under the plus code. -/
example :
    key {} integer .leadingPlus = "ZAHL_ENTHAELT_PLUS" ∧
      key {} { integer with signed := false } .leadingPlus = "ZAHL_ENTHAELT_VORZEICHEN" ∧
      key { amount := true } { integer with signed := false } .leadingPlus = "GBOC_ENTHAELT_VORZEICHEN" ∧
      NumericFormalReadError.leadingPlus.errorCode = "zahlMitPlus" := by
  native_decide

/- The integer-digit key carries the integer-only variant on a plain integer, and the zero refusal
   leaves both money families for the plain zero keys. -/
example :
    key {} integer .integerDigitsTooLong = "ZAHL_ZUVIELE_VORKOMMASTELLEN_MVZONK" ∧
      key {} twoPlaces .integerDigitsTooLong = "ZAHL_ZUVIELE_VORKOMMASTELLEN_MVZ" ∧
      key { amount := true, minFractionalDigits := 2 } twoPlaces .zeroNotAllowed = "ZAHL_IST_NULL" ∧
      key { amount := true } { integer with signed := false } .zeroNotAllowed = "ZAHL_IST_NULL_OVZ" := by
  native_decide

/- The universal digit ceiling is art-independent, unlike every other refusal above. -/
example :
    [key {} integer .totalDigitsTooLong,
        key { amount := true, minFractionalDigits := 2 } twoPlaces .totalDigitsTooLong,
        key { amount := true } integer .totalDigitsTooLong] =
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
