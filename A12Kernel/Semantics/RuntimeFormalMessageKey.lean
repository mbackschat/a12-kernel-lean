import A12Kernel.Semantics.NumberFormalCheck

/-! # Runtime formal-error message keys and their parameter contract

A runtime formal refusal surfaces two things independently: the **code**, owned by
`NumberFormalCheck` and its siblings, and the **message**, selected from the Kernel's own
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
fractional places, while it names the type for cents at any nonzero count, so a one- or three-place
money field is `moneyWithoutCents` here and `GeldBetragMitCent` there. -/
inductive NumberArt where
  | plain
  | moneyWithCents
  | moneyWithoutCents
  deriving Repr, DecidableEq, Inhabited

/-- Read the message family off the declaration. -/
def NumberFormalDeclaration.art (declaration : NumberFormalDeclaration) : NumberArt :=
  if !declaration.amount then .plain
  else if declaration.minFractionalDigits == 2 then .moneyWithCents
  else .moneyWithoutCents

/-- The message key a Number refusal selects, given its declaration.

Two facts here are invisible from the catalog alone and are what a reimplementer gets wrong. The
unreadable-value and fractional-count refusals split their key by **sign**, so one refusal on one art
still has two keys. And the zero refusal **leaves its own family**: on a money declaration it selects
the plain `ZAHL_IST_NULL` keys rather than a with- or without-cents one, which is the single place the
three families are not parallel. -/
def numberMessageKey (declaration : NumberFormalDeclaration) :
    NumberFormalRefusal → RuntimeFormalMessageKey :=
  let signed := !declaration.positivesOnly
  fun refusal =>
    match declaration.art, refusal with
    | _, .tooManyDigits => .textStelligkeitZuLang
    | .plain, .unreadable => .textZahlMitUngueltigenZeichen
    | .plain, .signedValue => .textZahlEnthaeltVorzeichen
    | .plain, .separatorNotAllowed => .textZahlHatDezimaltrenner
    | .plain, .fractionalDigitCount => .textZahlMitUngueltigenZeichen
    | .plain, .tooManyIntegerDigits =>
        if signed then .textZahlZuvieleVorkommastellenMvz else .textZahlZuvieleVorkommastellenOvz
    | .plain, .zeroNotAllowed => if signed then .textZahlIstNull else .textZahlIstNullOvz
    | .plain, .tooShort => .textZahlZuKurz
    | .plain, .tooLong => .textZahlZuLang
    | .plain, .belowMinimum => .textZahlZuKlein
    | .plain, .aboveMaximum => .textZahlZuGross
    | .moneyWithCents, .unreadable =>
        if signed then .textGbmcMitUngueltigenZeichenMvz else .textGbmcMitUngueltigenZeichenOvz
    | .moneyWithCents, .signedValue => .textGbmcEnthaeltVorzeichen
    | .moneyWithCents, .separatorNotAllowed => .textZahlHatDezimaltrenner
    | .moneyWithCents, .fractionalDigitCount =>
        if signed then .textGbmcMitUngueltigenZeichenMvz else .textGbmcMitUngueltigenZeichenOvz
    | .moneyWithCents, .tooManyIntegerDigits =>
        if signed then .textGbmcZuvieleVorkommastellenMvz else .textGbmcZuvieleVorkommastellenOvz
    | .moneyWithCents, .zeroNotAllowed => if signed then .textZahlIstNull else .textZahlIstNullOvz
    | .moneyWithCents, .tooShort => .textGbmcZuKurz
    | .moneyWithCents, .tooLong => .textGbmcZuLang
    | .moneyWithCents, .belowMinimum => .textGbmcZuKlein
    | .moneyWithCents, .aboveMaximum => .textGbmcZuGross
    | .moneyWithoutCents, .unreadable =>
        if signed then .textGbocMitUngueltigenZeichenMvz else .textGbocMitUngueltigenZeichenOvz
    | .moneyWithoutCents, .signedValue => .textGbocEnthaeltVorzeichen
    | .moneyWithoutCents, .separatorNotAllowed => .textZahlHatDezimaltrenner
    | .moneyWithoutCents, .fractionalDigitCount =>
        if signed then .textGbocMitUngueltigenZeichenMvz else .textGbocMitUngueltigenZeichenOvz
    | .moneyWithoutCents, .tooManyIntegerDigits =>
        if signed then .textGbocZuvieleVorkommastellenMvz else .textGbocZuvieleVorkommastellenOvz
    | .moneyWithoutCents, .zeroNotAllowed => if signed then .textZahlIstNull else .textZahlIstNullOvz
    | .moneyWithoutCents, .tooShort => .textGbocZuKurz
    | .moneyWithoutCents, .tooLong => .textGbocZuLang
    | .moneyWithoutCents, .belowMinimum => .textGbocZuKlein
    | .moneyWithoutCents, .aboveMaximum => .textGbocZuGross

end A12Kernel
