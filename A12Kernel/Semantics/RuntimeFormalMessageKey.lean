import A12Kernel.Semantics.NumericInput

/-! # Runtime formal-error message keys and their parameter contract

A runtime formal refusal surfaces two things independently: the **code**, owned by
`NumericInput`'s formal-read cascade and its siblings, and the **message**, selected from the Kernel's own
runtime formal-error bundle. This capsule owns the message side's structure — which bundle key a
refusal selects, and which parameters that key interpolates.

**The rendered English text is deliberately absent, and its absence is a licence boundary rather than
an omission.** The Kernel's message catalog is EUPL-licensed authored prose; this project is MIT and
reimplements behaviour clean-room, so it copies the mechanism and never the expression. A key and its
parameter list are functional identifiers — what a consumer must compute — while the sentence is a
localisation resource that consumer reads from the Kernel's own bundle or translates itself. Modelling
the key and its parameters therefore gives a reimplementer everything they cannot derive, and copying
the sentence would give them only something they must not take from us.

What this establishes is the **contract**: the closed key vocabulary, each key's parameter set, and the
number family's selection rule. What it does not establish is the selection rule for the date, string
and boolean families, whose keys are declared here with their parameters but whose choice function is
unmeasured; `docs/SEMANTICS-GAPS.md` carries that as an open obligation. The **addressing** family is no
longer among them on its over-maximum arm: [`AddressFormalLegality`](../Elaboration/AddressFormalLegality.lean)
owns the positional rule that picks the code, and the accompanying key is its parallel.
-/

namespace A12Kernel

/-- The values a formal-error message interpolates. Each names a quantity the consumer must supply
from the field's declaration, the offending value, or the addressing context — never free text. -/
inductive RuntimeFormalMessageParameter where
  | dateFormat
  | dateString
  | dateStringDay
  | dateStringMonth
  | dateStringYear
  | decimalSeparator
  | falseValue
  | fieldName
  | fieldPathName
  | groupIndexSpecified
  | groupName
  | maxGroupIndex
  | maxLength
  | maxNumberOfDecimalPlaces
  | maxValue
  | minLength
  | minValue
  | numberOfDecimalPlaces
  | numberOfDigitsBeforeDecimalPoint
  | numberOfIndicesExpected
  | numberOfIndicesSpecified
  | timeIntervalFormat
  | trueValue
  | zeros
  deriving Repr, DecidableEq, Inhabited

/-- The closed key vocabulary of the runtime formal-error bundle. Constructors carry a `text` prefix
so that no constructor name coincides with a surfaced error code: the two vocabularies overlap in
spelling — `ZAHL_ZU_LANG` against the code `zahlZuLang` — and conflating them is the exact mistake
this capsule exists to prevent. -/
inductive RuntimeFormalMessageKey where
  | textKeinFehler
  | textZahlMitUngueltigenZeichenOnk
  | textZahlMitUngueltigenZeichenFnkovz
  | textZahlMitUngueltigenZeichenFnkpvz
  | textZahlMitUngueltigenZeichenVnk
  | textZahlMitUngueltigenZeichen
  | textStelligkeitZuLang
  | textZahlEnthaeltVorzeichen
  | textZahlEnthaeltPlus
  | textZahlHatDezimaltrenner
  | textZahlNullEnthaeltVorzeichen
  | textZahlZuvieleVorkommastellenOvz
  | textZahlZuvieleVorkommastellenMvz
  | textZahlZuvieleVorkommastellenOvzonk
  | textZahlZuvieleVorkommastellenMvzonk
  | textZahlIstNullOvz
  | textZahlIstNull
  | textZahlHatFuehrendeNullen
  | textZahlZuKurz
  | textZahlZuLang
  | textZahlZuKlein
  | textZahlZuGross
  | textGbocMitUngueltigenZeichenOvz
  | textGbocMitUngueltigenZeichenMvz
  | textGbocEnthaeltVorzeichen
  | textGbocEnthaeltPlus
  | textGbocNullEnthaeltVorzeichen
  | textGbocZuvieleVorkommastellenOvz
  | textGbocZuvieleVorkommastellenMvz
  | textGbocHatFuehrendeNullen
  | textGbocZuKurz
  | textGbocZuLang
  | textGbocZuKlein
  | textGbocZuGross
  | textGbmcMitUngueltigenZeichenOvz
  | textGbmcMitUngueltigenZeichenMvz
  | textGbmcEnthaeltVorzeichen
  | textGbmcEnthaeltPlus
  | textGbmcNullEnthaeltVorzeichen
  | textGbmcZuvieleVorkommastellenOvz
  | textGbmcZuvieleVorkommastellenMvz
  | textGbmcHatFuehrendeNullen
  | textGbmcZuKurz
  | textGbmcZuLang
  | textGbmcZuKlein
  | textGbmcZuGross
  | textStringZuKurz
  | textStringZuLang
  | textStringEnthaeltNewline
  | textFeldJaNein
  | textFeldJa
  | textDatumFormat
  | textDatum
  | textDatumAdditionalCheck
  | textDatumTagFehler
  | textDatumMonatFehler
  | textDatumFebruar29Fehler
  | textDatumMonatFehlt
  | textDatumMonatFehlt0
  | textDatumJahrFehlt
  | textDatumMonatoptionalTagAngegeben
  | textDatumMonatoptionalTagAngegeben0
  | textDatumJahroptionalMonatOderTagAngegeben
  | textDatumMonat0
  | textDatumTag0
  | textDatumTag0Statt00
  | textDatumMonat0Statt00
  | textDatumBereichFormat
  | textDatumBereichNichtGueltig
  | textDatumBereichDatum
  | textDatumBereichDatumAdditionalCheck
  | textDatumBereichStartTagFehler
  | textDatumBereichStartMonatFehler
  | textDatumBereichStartFebruar29Fehler
  | textDatumBereichEndTagFehler
  | textDatumBereichEndMonatFehler
  | textDatumBereichEndFebruar29Fehler
  | textFehlerLaufendeNrFmText
  | textFehlerLaufendeNrZuGrossFmText
  | textFehlerZeileFmText
  | textFehlerZeilennummerZuGrossFmText
  | textFehlerUsbFmText
  | textFehlerUsbZuGrossFmText
  | textFehlerKeinUsbFmText
  | textFehlerUsbAngegebenFmText
  | textFehlerWertZuLangFmText
  | textFehlerFuehrendesBlankFmText
  | textFehlerNachfolgendesBlankFmText
  | textFehlerFeldUnbekannt
  | textZeichenNichtImZeichensatzFmText
  | textFalscheAnzahlIndicesFmText
  | textKontextnummerZuKleinFmText
  | textFehlerKontextnummerZuGrossFmText
  | textBerechnungWertFehler
  | textPflichtFeldFehler
  | textIndexFeldFehler
  | textEnumerationDefaultError
  | textSolitaryIndexFehler
  deriving Repr, DecidableEq, Inhabited

namespace RuntimeFormalMessageKey

/-- The Kernel's bundle key and the parameters its text interpolates, paired so the two cannot drift.
Derived mechanically from the Kernel's `error_messages_en.properties`: the key is its property name and
the parameters are its placeholder occurrences, so neither reproduces the message sentence. -/
def descriptor : RuntimeFormalMessageKey → String × List RuntimeFormalMessageParameter
  | .textKeinFehler => ("KEIN_FEHLER", [])
  | .textZahlMitUngueltigenZeichenOnk => ("ZAHL_MIT_UNGUELTIGEN_ZEICHEN_ONK", [])
  | .textZahlMitUngueltigenZeichenFnkovz => ("ZAHL_MIT_UNGUELTIGEN_ZEICHEN_FNKOVZ", [.decimalSeparator, .numberOfDecimalPlaces, .zeros])
  | .textZahlMitUngueltigenZeichenFnkpvz => ("ZAHL_MIT_UNGUELTIGEN_ZEICHEN_FNKPVZ", [.decimalSeparator, .numberOfDecimalPlaces, .zeros])
  | .textZahlMitUngueltigenZeichenVnk => ("ZAHL_MIT_UNGUELTIGEN_ZEICHEN_VNK", [.maxNumberOfDecimalPlaces, .numberOfDecimalPlaces])
  | .textZahlMitUngueltigenZeichen => ("ZAHL_MIT_UNGUELTIGEN_ZEICHEN", [])
  | .textStelligkeitZuLang => ("STELLIGKEIT_ZU_LANG", [])
  | .textZahlEnthaeltVorzeichen => ("ZAHL_ENTHAELT_VORZEICHEN", [])
  | .textZahlEnthaeltPlus => ("ZAHL_ENTHAELT_PLUS", [])
  | .textZahlHatDezimaltrenner => ("ZAHL_HAT_DEZIMALTRENNER", [])
  | .textZahlNullEnthaeltVorzeichen => ("ZAHL_NULL_ENTHAELT_VORZEICHEN", [])
  | .textZahlZuvieleVorkommastellenOvz => ("ZAHL_ZUVIELE_VORKOMMASTELLEN_OVZ", [.numberOfDigitsBeforeDecimalPoint])
  | .textZahlZuvieleVorkommastellenMvz => ("ZAHL_ZUVIELE_VORKOMMASTELLEN_MVZ", [.numberOfDigitsBeforeDecimalPoint])
  | .textZahlZuvieleVorkommastellenOvzonk => ("ZAHL_ZUVIELE_VORKOMMASTELLEN_OVZONK", [.numberOfDigitsBeforeDecimalPoint])
  | .textZahlZuvieleVorkommastellenMvzonk => ("ZAHL_ZUVIELE_VORKOMMASTELLEN_MVZONK", [.numberOfDigitsBeforeDecimalPoint])
  | .textZahlIstNullOvz => ("ZAHL_IST_NULL_OVZ", [])
  | .textZahlIstNull => ("ZAHL_IST_NULL", [])
  | .textZahlHatFuehrendeNullen => ("ZAHL_HAT_FUEHRENDE_NULLEN", [])
  | .textZahlZuKurz => ("ZAHL_ZU_KURZ", [.minLength])
  | .textZahlZuLang => ("ZAHL_ZU_LANG", [.maxLength])
  | .textZahlZuKlein => ("ZAHL_ZU_KLEIN", [.minValue])
  | .textZahlZuGross => ("ZAHL_ZU_GROSS", [.maxValue])
  | .textGbocMitUngueltigenZeichenOvz => ("GBOC_MIT_UNGUELTIGEN_ZEICHEN_OVZ", [])
  | .textGbocMitUngueltigenZeichenMvz => ("GBOC_MIT_UNGUELTIGEN_ZEICHEN_MVZ", [])
  | .textGbocEnthaeltVorzeichen => ("GBOC_ENTHAELT_VORZEICHEN", [])
  | .textGbocEnthaeltPlus => ("GBOC_ENTHAELT_PLUS", [])
  | .textGbocNullEnthaeltVorzeichen => ("GBOC_NULL_ENTHAELT_VORZEICHEN", [])
  | .textGbocZuvieleVorkommastellenOvz => ("GBOC_ZUVIELE_VORKOMMASTELLEN_OVZ", [.numberOfDigitsBeforeDecimalPoint])
  | .textGbocZuvieleVorkommastellenMvz => ("GBOC_ZUVIELE_VORKOMMASTELLEN_MVZ", [.numberOfDigitsBeforeDecimalPoint])
  | .textGbocHatFuehrendeNullen => ("GBOC_HAT_FUEHRENDE_NULLEN", [])
  | .textGbocZuKurz => ("GBOC_ZU_KURZ", [.minLength])
  | .textGbocZuLang => ("GBOC_ZU_LANG", [.maxLength])
  | .textGbocZuKlein => ("GBOC_ZU_KLEIN", [.minValue])
  | .textGbocZuGross => ("GBOC_ZU_GROSS", [.maxValue])
  | .textGbmcMitUngueltigenZeichenOvz => ("GBMC_MIT_UNGUELTIGEN_ZEICHEN_OVZ", [.decimalSeparator])
  | .textGbmcMitUngueltigenZeichenMvz => ("GBMC_MIT_UNGUELTIGEN_ZEICHEN_MVZ", [.decimalSeparator])
  | .textGbmcEnthaeltVorzeichen => ("GBMC_ENTHAELT_VORZEICHEN", [])
  | .textGbmcEnthaeltPlus => ("GBMC_ENTHAELT_PLUS", [.decimalSeparator])
  | .textGbmcNullEnthaeltVorzeichen => ("GBMC_NULL_ENTHAELT_VORZEICHEN", [.decimalSeparator])
  | .textGbmcZuvieleVorkommastellenOvz => ("GBMC_ZUVIELE_VORKOMMASTELLEN_OVZ", [.numberOfDigitsBeforeDecimalPoint])
  | .textGbmcZuvieleVorkommastellenMvz => ("GBMC_ZUVIELE_VORKOMMASTELLEN_MVZ", [.numberOfDigitsBeforeDecimalPoint])
  | .textGbmcHatFuehrendeNullen => ("GBMC_HAT_FUEHRENDE_NULLEN", [])
  | .textGbmcZuKurz => ("GBMC_ZU_KURZ", [.minLength])
  | .textGbmcZuLang => ("GBMC_ZU_LANG", [.maxLength])
  | .textGbmcZuKlein => ("GBMC_ZU_KLEIN", [.minValue])
  | .textGbmcZuGross => ("GBMC_ZU_GROSS", [.maxValue])
  | .textStringZuKurz => ("STRING_ZU_KURZ", [.minLength])
  | .textStringZuLang => ("STRING_ZU_LANG", [.maxLength])
  | .textStringEnthaeltNewline => ("STRING_ENTHAELT_NEWLINE", [])
  | .textFeldJaNein => ("FELD_JA_NEIN", [.falseValue, .trueValue])
  | .textFeldJa => ("FELD_JA", [.trueValue])
  | .textDatumFormat => ("DATUM_FORMAT", [.dateFormat])
  | .textDatum => ("DATUM", [.dateFormat])
  | .textDatumAdditionalCheck => ("DATUM_ADDITIONAL_CHECK", [.dateFormat])
  | .textDatumTagFehler => ("DATUM_TAG_FEHLER", [.dateFormat, .dateString, .dateStringDay])
  | .textDatumMonatFehler => ("DATUM_MONAT_FEHLER", [.dateFormat, .dateStringMonth])
  | .textDatumFebruar29Fehler => ("DATUM_FEBRUAR_29_FEHLER", [.dateFormat, .dateString, .dateStringYear])
  | .textDatumMonatFehlt => ("DATUM_MONAT_FEHLT", [])
  | .textDatumMonatFehlt0 => ("DATUM_MONAT_FEHLT0", [])
  | .textDatumJahrFehlt => ("DATUM_JAHR_FEHLT", [])
  | .textDatumMonatoptionalTagAngegeben => ("DATUM_MONATOPTIONAL_TAG_ANGEGEBEN", [])
  | .textDatumMonatoptionalTagAngegeben0 => ("DATUM_MONATOPTIONAL_TAG_ANGEGEBEN0", [])
  | .textDatumJahroptionalMonatOderTagAngegeben => ("DATUM_JAHROPTIONAL_MONAT_ODER_TAG_ANGEGEBEN", [])
  | .textDatumMonat0 => ("DATUM_MONAT_0", [])
  | .textDatumTag0 => ("DATUM_TAG_0", [])
  | .textDatumTag0Statt00 => ("DATUM_TAG_0_STATT_00", [])
  | .textDatumMonat0Statt00 => ("DATUM_MONAT_0_STATT_00", [])
  | .textDatumBereichFormat => ("DATUM_BEREICH_FORMAT", [.timeIntervalFormat])
  | .textDatumBereichNichtGueltig => ("DATUM_BEREICH_NICHT_GUELTIG", [.timeIntervalFormat])
  | .textDatumBereichDatum => ("DATUM_BEREICH_DATUM", [.timeIntervalFormat])
  | .textDatumBereichDatumAdditionalCheck => ("DATUM_BEREICH_DATUM_ADDITIONAL_CHECK", [.timeIntervalFormat])
  | .textDatumBereichStartTagFehler => ("DATUM_BEREICH_START_TAG_FEHLER", [.dateString, .dateStringDay, .timeIntervalFormat])
  | .textDatumBereichStartMonatFehler => ("DATUM_BEREICH_START_MONAT_FEHLER", [.dateStringMonth, .timeIntervalFormat])
  | .textDatumBereichStartFebruar29Fehler => ("DATUM_BEREICH_START_FEBRUAR_29_FEHLER", [.dateString, .dateStringYear, .timeIntervalFormat])
  | .textDatumBereichEndTagFehler => ("DATUM_BEREICH_END_TAG_FEHLER", [.dateString, .dateStringDay, .timeIntervalFormat])
  | .textDatumBereichEndMonatFehler => ("DATUM_BEREICH_END_MONAT_FEHLER", [.dateStringMonth, .timeIntervalFormat])
  | .textDatumBereichEndFebruar29Fehler => ("DATUM_BEREICH_END_FEBRUAR_29_FEHLER", [.dateString, .dateStringYear, .timeIntervalFormat])
  | .textFehlerLaufendeNrFmText => ("FEHLER_LAUFENDE_NR_FM_TEXT", [])
  | .textFehlerLaufendeNrZuGrossFmText => ("FEHLER_LAUFENDE_NR_ZU_GROSS_FM_TEXT", [])
  | .textFehlerZeileFmText => ("FEHLER_ZEILE_FM_TEXT", [])
  | .textFehlerZeilennummerZuGrossFmText => ("FEHLER_ZEILENNUMMER_ZU_GROSS_FM_TEXT", [])
  | .textFehlerUsbFmText => ("FEHLER_USB_FM_TEXT", [])
  | .textFehlerUsbZuGrossFmText => ("FEHLER_USB_ZU_GROSS_FM_TEXT", [])
  | .textFehlerKeinUsbFmText => ("FEHLER_KEIN_USB_FM_TEXT", [])
  | .textFehlerUsbAngegebenFmText => ("FEHLER_USB_ANGEGEBEN_FM_TEXT", [])
  | .textFehlerWertZuLangFmText => ("FEHLER_WERT_ZU_LANG_FM_TEXT", [])
  | .textFehlerFuehrendesBlankFmText => ("FEHLER_FUEHRENDES_BLANK_FM_TEXT", [])
  | .textFehlerNachfolgendesBlankFmText => ("FEHLER_NACHFOLGENDES_BLANK_FM_TEXT", [])
  | .textFehlerFeldUnbekannt => ("FEHLER_FELD_UNBEKANNT", [])
  | .textZeichenNichtImZeichensatzFmText => ("ZEICHEN_NICHT_IM_ZEICHENSATZ_FM_TEXT", [])
  | .textFalscheAnzahlIndicesFmText => ("FALSCHE_ANZAHL_INDICES_FM_TEXT", [.fieldPathName, .numberOfIndicesExpected, .numberOfIndicesSpecified])
  | .textKontextnummerZuKleinFmText => ("KONTEXTNUMMER_ZU_KLEIN_FM_TEXT", [.groupIndexSpecified, .groupName])
  | .textFehlerKontextnummerZuGrossFmText => ("FEHLER_KONTEXTNUMMER_ZU_GROSS_FM_TEXT", [.groupIndexSpecified, .groupName, .maxGroupIndex])
  | .textBerechnungWertFehler => ("BERECHNUNG_WERT_FEHLER", [])
  | .textPflichtFeldFehler => ("PFLICHT_FELD_FEHLER", [])
  | .textIndexFeldFehler => ("INDEX_FELD_FEHLER", [])
  | .textEnumerationDefaultError => ("ENUMERATION_DEFAULT_ERROR", [])
  | .textSolitaryIndexFehler => ("SOLITARY_INDEX_FEHLER", [.fieldName])

/-- The Kernel's property name for this key. -/
def bundleKey (key : RuntimeFormalMessageKey) : String := key.descriptor.1

/-- The values this key's text interpolates, in the Kernel catalog's own order. -/
def parameters (key : RuntimeFormalMessageKey) : List RuntimeFormalMessageParameter :=
  key.descriptor.2

end RuntimeFormalMessageKey

/-- Which of the three message families a Number declaration draws its text from. This is **not** the
same split as the field-type name: the Kernel selects the with-cents family at exactly two declared
minimum fractional places, while it names the type for cents at any nonzero count, so a one- or
three-place money field is `moneyWithoutCents` here and `GeldBetragMitCent` there. -/
inductive NumberArt where
  | plain
  | moneyWithCents
  | moneyWithoutCents
  deriving Repr, DecidableEq, Inhabited

/-- How a plain Number declares its fractional places, which splits the unreadable-text keys. Over
nonnegative members the admission gate keeps the minimum at or below the maximum (`info.scale`), so
these three cases are exhaustive there. The Kernel's bare fallback key belongs to the `-1` no-bound
sentinel, which the DM reader refuses rather than represent. -/
inductive NumberFractionShape where
  | integer
  | variable
  | fixed
  deriving Repr, DecidableEq, Inhabited

namespace NumericTargetConstraints

/-- Read the message family off the declaration's amount trait and minimum fractional places. -/
def art (constraints : NumericTargetConstraints) : NumberArt :=
  if !constraints.amount then .plain
  else if constraints.minFractionalDigits == 2 then .moneyWithCents
  else .moneyWithoutCents

/-- Read the fractional shape off the declared minimum and maximum (`info.scale`) places. -/
def fractionShape (constraints : NumericTargetConstraints) (info : NumField) : NumberFractionShape :=
  if constraints.minFractionalDigits < info.scale then .variable
  else if constraints.minFractionalDigits == 0 then .integer
  else .fixed

end NumericTargetConstraints

/-- The message key a Number formal-read refusal selects, given its declaration.

The code is the refusal's alone (`NumericFormalReadError.errorCode`); the key additionally reads the
art, the declared sign and, for a plain Number, the fractional shape. Four facts here are invisible
from the catalog and are what a reimplementer gets wrong. The plus refusal on an unsigned
declaration selects the sign key, not the plus key. The unreadable-text, missing-separator and
fractional-count refusals share one key per art, which on a plain Number is split by fractional
shape and on a money Number by declared sign. The separator refusal leaves its key on a money
Number, joining the unreadable-text key there. And the zero refusal leaves its family altogether: on
both money arts it selects the plain `ZAHL_IST_NULL` keys.

Basis: read from the 30.8.1 runtime Number format's per-art key choice
([checkpoint](../../docs/sources/domain-ingestion-probes.md#src-number-ingress-k16)); each arm the K16 capture reaches was
identified by its rendered text at measurement, which the retained artifact redacts. -/
def numberMessageKey (constraints : NumericTargetConstraints) (info : NumField) :
    NumericFormalReadError → RuntimeFormalMessageKey :=
  let signed := info.signed
  let bySign := fun (withSign withoutSign : RuntimeFormalMessageKey) =>
    if signed then withSign else withoutSign
  let zero := bySign .textZahlIstNull .textZahlIstNullOvz
  fun error =>
    match constraints.art, error with
    | _, .totalDigitsTooLong => .textStelligkeitZuLang
    | _, .zeroNotAllowed => zero
    | .plain, .leadingPlus => bySign .textZahlEnthaeltPlus .textZahlEnthaeltVorzeichen
    | .plain, .malformed | .plain, .decimalSeparatorRequired
    | .plain, .fractionalDigitsOutOfRange =>
        match constraints.fractionShape info with
        | .integer => .textZahlMitUngueltigenZeichenOnk
        | .variable => .textZahlMitUngueltigenZeichenVnk
        | .fixed => bySign .textZahlMitUngueltigenZeichenFnkpvz .textZahlMitUngueltigenZeichenFnkovz
    | .plain, .negativeNotAllowed => .textZahlEnthaeltVorzeichen
    | .plain, .signedZero => .textZahlNullEnthaeltVorzeichen
    | .plain, .decimalSeparatorForbidden => .textZahlHatDezimaltrenner
    | .plain, .integerDigitsTooLong =>
        if constraints.fractionShape info == .integer then
          bySign .textZahlZuvieleVorkommastellenMvzonk .textZahlZuvieleVorkommastellenOvzonk
        else bySign .textZahlZuvieleVorkommastellenMvz .textZahlZuvieleVorkommastellenOvz
    | .plain, .leadingZerosNotAllowed => .textZahlHatFuehrendeNullen
    | .plain, .textTooShort => .textZahlZuKurz
    | .plain, .textTooLong => .textZahlZuLang
    | .plain, .belowMinimum => .textZahlZuKlein
    | .plain, .aboveMaximum => .textZahlZuGross
    | .moneyWithCents, .leadingPlus => bySign .textGbmcEnthaeltPlus .textGbmcEnthaeltVorzeichen
    | .moneyWithCents, .malformed | .moneyWithCents, .decimalSeparatorRequired
    | .moneyWithCents, .fractionalDigitsOutOfRange =>
        bySign .textGbmcMitUngueltigenZeichenMvz .textGbmcMitUngueltigenZeichenOvz
    -- The with-cents family has no separator arm and falls to its catalog default, which does not
    -- read the sign; two declared places exclude the refusal in every admitted declaration.
    | .moneyWithCents, .decimalSeparatorForbidden => .textGbmcMitUngueltigenZeichenOvz
    | .moneyWithCents, .negativeNotAllowed => .textGbmcEnthaeltVorzeichen
    | .moneyWithCents, .signedZero => .textGbmcNullEnthaeltVorzeichen
    | .moneyWithCents, .integerDigitsTooLong =>
        bySign .textGbmcZuvieleVorkommastellenMvz .textGbmcZuvieleVorkommastellenOvz
    | .moneyWithCents, .leadingZerosNotAllowed => .textGbmcHatFuehrendeNullen
    | .moneyWithCents, .textTooShort => .textGbmcZuKurz
    | .moneyWithCents, .textTooLong => .textGbmcZuLang
    | .moneyWithCents, .belowMinimum => .textGbmcZuKlein
    | .moneyWithCents, .aboveMaximum => .textGbmcZuGross
    | .moneyWithoutCents, .leadingPlus => bySign .textGbocEnthaeltPlus .textGbocEnthaeltVorzeichen
    | .moneyWithoutCents, .malformed | .moneyWithoutCents, .decimalSeparatorForbidden
    | .moneyWithoutCents, .decimalSeparatorRequired
    | .moneyWithoutCents, .fractionalDigitsOutOfRange =>
        bySign .textGbocMitUngueltigenZeichenMvz .textGbocMitUngueltigenZeichenOvz
    | .moneyWithoutCents, .negativeNotAllowed => .textGbocEnthaeltVorzeichen
    | .moneyWithoutCents, .signedZero => .textGbocNullEnthaeltVorzeichen
    | .moneyWithoutCents, .integerDigitsTooLong =>
        bySign .textGbocZuvieleVorkommastellenMvz .textGbocZuvieleVorkommastellenOvz
    | .moneyWithoutCents, .leadingZerosNotAllowed => .textGbocHatFuehrendeNullen
    | .moneyWithoutCents, .textTooShort => .textGbocZuKurz
    | .moneyWithoutCents, .textTooLong => .textGbocZuLang
    | .moneyWithoutCents, .belowMinimum => .textGbocZuKlein
    | .moneyWithoutCents, .aboveMaximum => .textGbocZuGross

end A12Kernel
