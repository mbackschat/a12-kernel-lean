import A12Kernel.Elaboration.FormalMessageKeys

/-! # Component-omitting, clock, unsigned Number and addressing message-key locks

Each case is one row of the wider K22 key runs
([checkpoint](../../docs/sources/domain-ingestion-probes.md#src-k22-formal-keys-wider)), whose key was
identified by its rendered text at measurement and retained by name in the capture's `keys.json`. Where
two keys render one sentence, the row names the one its code and declaration select. The rows separate
the accounts a reimplementer gets wrong: one component reading for every format rather than a month
check per format, a day-free format's month as a format defect, a clock failure as the date's day
defect, and the pre-1900 check ahead of every component of a malformed date. -/

namespace A12Kernel.Conformance.FormalMessageKeys

open A12Kernel

private def omitting (format : OmittingDateFormat) (baseYear : Option Int) (check : Bool)
    (text : String) : Option String :=
  (format.messageKey? baseYear check text).map (·.bundleKey)

private def dateTime (text : String) : Option String :=
  match DateTimeTargetFormat.yearMonthDayTime.messageKey? ModelZone.ConcreteProfile.europeBerlin text with
  | .ok key => key.map (·.bundleKey)
  | .error _ => some "error"

private def full (check : Bool) (format : FullDateInputFormat) (text : String) : Option String :=
  (format.dateMessageKey? .full check text).map (·.bundleKey)

/- `Y`, `YM`, `YMc`, `Mo` and `YC`: a format without a day takes the format key for every refusal,
   month `13` included, and the date keys only for a real date before 1900 or the floor. -/
example :
    [(OmittingDateFormat.year, "20x6", "DATUM_FORMAT"), (.year, "026", "DATUM_FORMAT"), (.year, "0000", "DATUM_FORMAT"),
      (.year, "1500", "DATUM"), (.year, "99999", "DATUM_FORMAT"), (.yearMonthDashed, "2026-13", "DATUM_FORMAT"),
      (.yearMonthDashed, "2026-00", "DATUM_FORMAT"), (.yearMonthDashed, "2026-1", "DATUM_FORMAT"),
      (.yearMonthDashed, "0000-05", "DATUM_FORMAT"), (.yearMonthDashed, "1500-05", "DATUM"),
      (.yearMonthConcatenated, "202613", "DATUM_FORMAT"), (.yearMonthConcatenated, "202600", "DATUM_FORMAT"),
      (.yearMonthConcatenated, "20261", "DATUM_FORMAT"), (.month, "13", "DATUM_FORMAT"), (.month, "00", "DATUM_FORMAT"),
      (.month, "1", "DATUM_FORMAT"), (.month, "x1", "DATUM_FORMAT")].all
      (fun (format, text, key) => omitting format none false text == some key) ∧
    omitting .year none true "1850" = some "DATUM_ADDITIONAL_CHECK" ∧ omitting .year none true "2026" = none := by
  native_decide

/- `MD`, `MDc`, `DMc` and `DMd` without a Base Year, then under Base Year 2025: a day-bearing format
   takes the component keys, and `02-29` is admitted until a common Base Year makes it the leap-day
   defect. -/
example :
    [(OmittingDateFormat.monthDay, "13-01", some "DATUM_MONAT_FEHLER"), (.monthDay, "02-30", some "DATUM_TAG_FEHLER"),
      (.monthDay, "02-29", none), (.monthDay, "00-05", some "DATUM_FORMAT"), (.monthDay, "05-00", some "DATUM_FORMAT"),
      (.monthDay, "04-31", some "DATUM_TAG_FEHLER"), (.monthDay, "2-3", some "DATUM_FORMAT"),
      (.monthDayConcatenated, "1301", some "DATUM_MONAT_FEHLER"), (.monthDayConcatenated, "0230", some "DATUM_TAG_FEHLER"),
      (.monthDayConcatenated, "0229", none), (.monthDayConcatenated, "0431", some "DATUM_TAG_FEHLER"),
      (.dayMonthConcatenated, "3002", some "DATUM_TAG_FEHLER"), (.dayMonthConcatenated, "2902", none),
      (.dayMonthConcatenated, "0113", some "DATUM_MONAT_FEHLER"), (.dayMonthConcatenated, "3104", some "DATUM_TAG_FEHLER"),
      (.dayMonthDotted, "30.02.", some "DATUM_TAG_FEHLER"), (.dayMonthDotted, "29.02.", none),
      (.dayMonthDotted, "01.13.", some "DATUM_MONAT_FEHLER"), (.dayMonthDotted, "31.04.", some "DATUM_TAG_FEHLER"),
      (.dayMonthDotted, "1.1.", some "DATUM_FORMAT"), (.dayMonthDotted, "30.02", some "DATUM_FORMAT")].all
      (fun (format, text, key) => omitting format none false text == key) ∧
    [(OmittingDateFormat.monthDay, "02-29", some "DATUM_FEBRUAR_29_FEHLER"), (.monthDay, "02-30", some "DATUM_TAG_FEHLER"),
      (.monthDay, "13-01", some "DATUM_MONAT_FEHLER"), (.monthDay, "02-28", none),
      (.monthDayConcatenated, "0229", some "DATUM_FEBRUAR_29_FEHLER"), (.monthDayConcatenated, "1301", some "DATUM_MONAT_FEHLER"),
      (.dayMonthConcatenated, "2902", some "DATUM_FEBRUAR_29_FEHLER"), (.dayMonthConcatenated, "3104", some "DATUM_TAG_FEHLER"),
      (.dayMonthDotted, "29.02.", some "DATUM_FEBRUAR_29_FEHLER"), (.dayMonthDotted, "30.02.", some "DATUM_TAG_FEHLER")].all
      (fun (format, text, key) => omitting format (some 2025) false text == key) := by
  native_decide

/- `DT` and `DD`: a well-shaped label whose clock fails reads its date half, so a sound date takes the
   day key, February 29 and month `13` keep theirs, and a zero part or a misshapen label the format
   key; a real date with a sound clock before the floor takes the date key. -/
example :
    [("2026-02-30T10:00:00", "DATUM_TAG_FEHLER"), ("2026-13-01T10:00:00", "DATUM_MONAT_FEHLER"),
      ("2026-01-01T25:00:00", "DATUM_TAG_FEHLER"), ("2026-01-01 10:00:00", "DATUM_FORMAT"),
      ("2025-02-29T10:00:00", "DATUM_FEBRUAR_29_FEHLER"), ("1500-01-01T10:00:00", "DATUM"),
      ("2026-01-01T10:60:00", "DATUM_TAG_FEHLER"), ("2026-01-01T10:00:60", "DATUM_TAG_FEHLER"),
      ("2026-01-01T24:00:00", "DATUM_TAG_FEHLER"), ("2025-02-29T25:00:00", "DATUM_FEBRUAR_29_FEHLER"),
      ("2026-13-01T25:00:00", "DATUM_MONAT_FEHLER"), ("0000-01-01T10:00:00", "DATUM_FORMAT"),
      ("1500-01-01T25:00:00", "DATUM_TAG_FEHLER"), ("2026-02-30T25:00:00", "DATUM_TAG_FEHLER"),
      ("2026-00-01T25:00:00", "DATUM_FORMAT"), ("2026-01-01", "DATUM_FORMAT")].all
      (fun (text, key) => dateTime text == some key) := by
  native_decide

/- `T` and `DH`: the clock format carries no day, so every refusal takes the format key. -/
example :
    ["24:00:00", "12:60:00", "12:00:60", "1:2:3", "12:00", "ab", "25:00:00"].all
      (fun text => clockFormatMessageKey? text == some .textDatumFormat) ∧
    clockFormatMessageKey? "10:00:00" = none := by
  native_decide

/- `D1`, `D2` and `TD`: on a malformed complete date the pre-1900 check answers ahead of every
   component and a zero part ahead of the check, and a Julian leap day of 1500 is real and below the
   floor; the format decides, so a Time field declared `yyyy-MM-dd` reads the same keys. -/
example :
    [("31.02.1850", "DATUM_ADDITIONAL_CHECK"), ("29.02.1899", "DATUM_ADDITIONAL_CHECK"), ("00.05.1850", "DATUM_FORMAT"),
      ("1.1.1850", "DATUM_FORMAT"), ("31.13.1850", "DATUM_ADDITIONAL_CHECK")].all
      (fun (text, key) => full true .dayMonthYearDots text == some key) ∧
    [("1500-02-30", "DATUM_TAG_FEHLER"), ("1500-13-01", "DATUM_MONAT_FEHLER"), ("1500-02-29", "DATUM"),
      ("1000-01-01", "DATUM"), ("0000-01-01", "DATUM_FORMAT"), ("2026-13-01", "DATUM_MONAT_FEHLER"),
      ("2026-02-30", "DATUM_TAG_FEHLER"), ("10:00:00", "DATUM_FORMAT")].all
      (fun (text, key) => full false .yearMonthDayDashes text == some key) := by
  native_decide

private def unsigned (scale : Nat) : NumField := { scale, signed := false }

/- `U0`, `U2`, `UV`, `UC`, `UO` and `UI`, all unsigned: each refusal's code and the key its declaration
   selects. `GBOC_MIT_UNGUELTIGEN_ZEICHEN_OVZ` and `ZAHL_ZUVIELE_VORKOMMASTELLEN_OVZONK` share their
   sentences with other keys; the code and the unsigned declaration name them. -/
example :
    [(({} : NumericTargetConstraints), unsigned 0, NumericFormalReadError.negativeNotAllowed, "zahlMitVorzeichen",
        "ZAHL_ENTHAELT_VORZEICHEN"),
      ({}, unsigned 0, .malformed, "zahlHatUngueltigeZeichen", "ZAHL_MIT_UNGUELTIGEN_ZEICHEN_ONK"),
      ({ minFractionalDigits := 2 }, unsigned 2, .negativeNotAllowed, "zahlMitVorzeichen", "ZAHL_ENTHAELT_VORZEICHEN"),
      ({ minFractionalDigits := 2 }, unsigned 2, .malformed, "zahlHatUngueltigeZeichen",
        "ZAHL_MIT_UNGUELTIGEN_ZEICHEN_FNKOVZ"),
      ({}, unsigned 2, .negativeNotAllowed, "zahlMitVorzeichen", "ZAHL_ENTHAELT_VORZEICHEN"),
      ({}, unsigned 2, .fractionalDigitsOutOfRange, "zahlFalscheAnzahlNachkommastellen",
        "ZAHL_MIT_UNGUELTIGEN_ZEICHEN_VNK"),
      ({ amount := true, minFractionalDigits := 2 }, unsigned 2, .negativeNotAllowed, "zahlMitVorzeichen",
        "GBMC_ENTHAELT_VORZEICHEN"),
      ({ amount := true, minFractionalDigits := 2 }, unsigned 2, .malformed, "zahlHatUngueltigeZeichen",
        "GBMC_MIT_UNGUELTIGEN_ZEICHEN_OVZ"),
      ({ amount := true }, unsigned 0, .negativeNotAllowed, "zahlMitVorzeichen", "GBOC_ENTHAELT_VORZEICHEN"),
      ({ amount := true }, unsigned 0, .malformed, "zahlHatUngueltigeZeichen", "GBOC_MIT_UNGUELTIGEN_ZEICHEN_OVZ"),
      ({ maxIntegerDigits := some 3 }, unsigned 0, .integerDigitsTooLong, "zahlZuvieleVorkommastellen",
        "ZAHL_ZUVIELE_VORKOMMASTELLEN_OVZONK")].all
      (fun (constraints, info, error, code, key) =>
        error.errorCode == code && (numberMessageKey constraints info error).bundleKey == key) := by
  native_decide

/- `lines3`, `sub3` and `lines3sub`: the over-maximum row and context codes and their keys. -/
example :
    AddressRefusal.rowTooLarge.code = "zuGrosseZeile" ∧
      AddressRefusal.rowTooLarge.messageKey.bundleKey = "FEHLER_ZEILENNUMMER_ZU_GROSS_FM_TEXT" ∧
      AddressRefusal.contextTooLarge.code = "zuGrosseKontextnummer" ∧
      AddressRefusal.contextTooLarge.messageKey.bundleKey = "FEHLER_KONTEXTNUMMER_ZU_GROSS_FM_TEXT" := by
  native_decide

end A12Kernel.Conformance.FormalMessageKeys
