import A12Kernel.Semantics.DateFormalMessageKey

/-! # Date, String, Boolean and Enumeration message-key locks

Each case is one row of the K22 message-key run
([checkpoint](../../docs/sources/domain-ingestion-probes.md#src-date-message-keys-k22)), whose key was
identified by its rendered text at measurement and retained by name in the capture's `keys.json`. The
rows separate the accounts a reimplementer gets wrong: the code alone, a calendar check before the
spelling check, the month before the pre-1900 check, and one key for both range endpoints. -/

namespace A12Kernel.Conformance.DateFormalMessageKey

open A12Kernel

private def date (mode : TemporalPartialMode) (check : Bool) (format : FullDateInputFormat)
    (text : String) : Option String :=
  (format.dateMessageKey? mode check text).map (·.bundleKey)

private def range (text : String) : Option String :=
  (FullDateInputFormat.yearMonthDayDashes.dateRangeMessageKey? "/" false text).map (·.bundleKey)

/- `D1`, a full `yyyy-MM-dd`: every syntactically sound unreal date selects a component key, the
   cutover gap day the day's, and only a zero part, a short part or a non-digit the format key. -/
example :
    [("2026-13-01", "DATUM_MONAT_FEHLER"), ("2026-02-30", "DATUM_TAG_FEHLER"),
      ("2025-02-29", "DATUM_FEBRUAR_29_FEHLER"), ("2024-02-30", "DATUM_TAG_FEHLER"),
      ("2026-04-31", "DATUM_TAG_FEHLER"), ("abc", "DATUM_FORMAT"), ("2026-1-01", "DATUM_FORMAT"),
      ("2026-00-10", "DATUM_FORMAT"), ("2026-03-00", "DATUM_FORMAT"), ("0000-03-10", "DATUM_FORMAT"),
      ("0999-01-01", "DATUM"), ("1582-10-10", "DATUM_TAG_FEHLER")].all
      (fun (text, key) => date .full false .yearMonthDayDashes text == some key) := by
  native_decide

/- `D2`, `dd.MM.yyyy` with the pre-1900 check: the check answers a real early date, and an unreal one
   ahead of its month. -/
example :
    [("01.01.1899", "DATUM_ADDITIONAL_CHECK"), ("30.02.1899", "DATUM_ADDITIONAL_CHECK"),
      ("31.04.2020", "DATUM_TAG_FEHLER"), ("13.13.1850", "DATUM_ADDITIONAL_CHECK")].all
      (fun (text, key) => date .full true .dayMonthYearDots text == some key) := by
  native_decide

/- `D3`–`D5`, the three partial precisions over `yyyy-MM-dd`: the omission table first, then the
   component reading of the completed date. -/
example :
    [(TemporalPartialMode.dayOptional, "2026-00-00", "DATUM_MONAT_FEHLT"),
      (.dayOptional, "2026-00-05", "DATUM_MONAT_FEHLT"), (.dayOptional, "0000-03-00", "DATUM_JAHR_FEHLT"),
      (.dayOptional, "2026-13-00", "DATUM_MONAT_FEHLER"),
      (.monthOptional, "2026-00-05", "DATUM_MONATOPTIONAL_TAG_ANGEGEBEN"),
      (.monthOptional, "0000-05-00", "DATUM_JAHR_FEHLT"), (.monthOptional, "0000-00-00", "DATUM_JAHR_FEHLT"),
      (.monthOptional, "2026-02-30", "DATUM_TAG_FEHLER"),
      (.yearOptional, "0000-05-01", "DATUM_JAHROPTIONAL_MONAT_ODER_TAG_ANGEGEBEN"),
      (.yearOptional, "0000-00-05", "DATUM_JAHROPTIONAL_MONAT_ODER_TAG_ANGEGEBEN"),
      (.yearOptional, "2026-00-05", "DATUM_MONATOPTIONAL_TAG_ANGEGEBEN"),
      (.yearOptional, "0000-13-00", "DATUM_JAHROPTIONAL_MONAT_ODER_TAG_ANGEGEBEN")].all
      (fun (mode, text, key) => date mode false .yearMonthDayDashes text == some key) := by
  native_decide

/- `R1`, a `yyyy-MM-dd` range split at `/`: each endpoint selects its own component key, a missing
   separator and an unreadable endpoint the range's format key. -/
example :
    [("2020-01-01/2019-12-31", "DATUM_BEREICH_NICHT_GUELTIG"),
      ("2020-13-01/2021-01-01", "DATUM_BEREICH_START_MONAT_FEHLER"),
      ("2020-01-01/2021-02-30", "DATUM_BEREICH_END_TAG_FEHLER"),
      ("2021-02-29/2021-03-01", "DATUM_BEREICH_START_FEBRUAR_29_FEHLER"),
      ("2020-01-01/2021-02-29", "DATUM_BEREICH_END_FEBRUAR_29_FEHLER"), ("2020-01-01", "DATUM_BEREICH_FORMAT"),
      ("xx/yy", "DATUM_BEREICH_FORMAT"), ("2020-04-31/2020-05-01", "DATUM_BEREICH_START_TAG_FEHLER"),
      ("0999-01-01/2020-01-01", "DATUM_BEREICH_DATUM")].all
      (fun (text, key) => range text == some key) := by
  native_decide

/- An admitted value selects no key, so the selection cannot fire where the formal check does not. -/
example :
    date .full false .yearMonthDayDashes "2026-02-28" = none ∧
      date .dayOptional false .yearMonthDayDashes "2026-03-00" = none ∧
      range "2020-01-01/2020-01-01" = none := by
  native_decide

/- `S1`, `B`, `C`, `E1`: the String, token and Enumeration keys. `S2` and `E2` render the
   declaration's own text, which no key names. -/
example :
    [StringFieldError.tooShort, .tooLong, .lineBreak].map (·.messageKey?.map (·.bundleKey)) =
        [some "STRING_ZU_KURZ", some "STRING_ZU_LANG", some "STRING_ENTHAELT_NEWLINE"] ∧
      StringFieldError.pattern.messageKey? = none ∧
      FormalCause.booleanToken.tokenMessageKey?.map (·.bundleKey) = some "FELD_JA_NEIN" ∧
      FormalCause.confirmToken.tokenMessageKey?.map (·.bundleKey) = some "FELD_JA" ∧
      (enumerationMessageKey? false).map (·.bundleKey) = some "ENUMERATION_DEFAULT_ERROR" ∧
      enumerationMessageKey? true = none := by
  native_decide

end A12Kernel.Conformance.DateFormalMessageKey
