/-! # The registered custom field types and their refusal vocabulary

A condition may ask whether a field's value is a valid instance of a named predefined type — a German tax number, an IBAN, an identification number. The Kernel ships validators for thirteen such types, and this module records their observable refusal vocabulary.

Like the runtime formal number checks, the family answers on **two independent axes**, and a consumer that collapses them gets a different answer than the Kernel does.

* The **surfaced code** is what a validation result carries. There are fourteen for thirteen types, because of the exception below, and it is what a consumer switches on.
* The **detail key** selects the message and names *which* of the type's checks refused. There are thirty-six, and a type has between one and six.

Neither axis is a function of the other, and both counterexamples are worth keeping because each defeats a plausible simplification:

* One type surfaces **two** codes. The identification number reports its own code for every refusal except one: a structurally valid number in the reserved test range surfaces a *separate* code, so a consumer keying off the code alone sees two unrelated failures where the Kernel sees one validator.
* One detail key belongs to **two** types. Both date types share a single refusal key, whose message carries the expected format as a parameter rather than spelling it per type — so the key does not identify the type and the code does.

Every check in this family runs at value-validation time. Static model checking accepts any type name, including one no validator is registered for, which is why this vocabulary is not part of [`StaticDiagnostic.lean`](../Elaboration/StaticDiagnostic.lean).

This complements rather than duplicates [`CustomFieldType.lean`](CustomFieldType.lean), which models the registered-validator interface itself — resolution from the world, the effective context, and the opaque rejection a *host*-supplied validator returns. That account is deliberately blind to which validator is registered, because a host may register its own. What it leaves open is the concrete content: the codes below are exactly the values a `RegisteredCustomRejection` carries when the registered validator is one the Kernel itself ships.

**Evidence status: `external evidence pending`.** The vocabulary and its mapping are read from the Kernel's validator sources and its catalog; no observation of a running validator is retained. What each type's checks are, and in what order they fire, is a separate obligation tracked at its own gap — this module records only which names exist and how the two axes relate. No rendered message text is carried here, by the licensing boundary in [`CLAUDE.md`](../../CLAUDE.md).
-/

namespace A12Kernel

/-- A predefined custom field type the Kernel ships a validator for. -/
inductive CustomFieldType where
  /-- German personal identification number. The only type that surfaces two codes. -/
  | identificationNumber
  /-- German tax number. -/
  | taxNumber
  /-- Unit-value file reference. -/
  | unitValueFileReference
  /-- Federal tax-office number. -/
  | taxOfficeNumber
  /-- Country abbreviation. -/
  | countryAbbreviation
  /-- German IBAN. -/
  | iban
  /-- International IBAN, a separate validator from the German one. -/
  | ibanInternational
  /-- German BIC. -/
  | bic
  /-- International BIC, a separate validator from the German one. -/
  | bicInternational
  /-- Two-digit month and year. -/
  | dateMonthYear
  /-- Two-digit day, month and year. -/
  | dateDayMonthYear
  /-- Federal tax number, a separate validator from the ordinary tax number. -/
  | federalTaxNumber
  /-- Criminal-proceedings file reference. -/
  | criminalFileReference
  deriving Repr, DecidableEq

/-- One of the thirty-six detail keys that select a refusal's message. -/
inductive CustomFieldTypeDetail where
  /-- The success sentinel. It is a member of the catalog rather than an absence, which matters to a
  consumer enumerating the catalog: it is the one key that never accompanies a refusal. -/
  | noError
  | bicFormat | bicCountryCode
  | bicInternationalFormat
  | taxOfficeNumberFormat | taxOfficeNumberInvalidOffice
  | federalTaxNumberInvalid
  | dateInvalid
  | unitValueOffice | unitValueFormat | unitValueFormatKey | unitValueCheckDigit
  | ibanFormat | ibanCountryCode | ibanCountryFormat | ibanCheckDigit | ibanWhitespace
  | ibanInternationalFormat | ibanInternationalCountryFormat | ibanInternationalCheckDigit
  | ibanInternationalWhitespace
  /-- Deprecated for removal since Kernel 30.6.0, and still the one detail that changes the code. -/
  | identificationNumberTestOnly
  | identificationNumberNotNumeric | identificationNumberDigitSequence
  | identificationNumberLength | identificationNumberCheckDigit
  | identificationNumberWhitespace
  | countryAbbreviationInvalid
  | taxNumberFormat | taxNumberOffice | taxNumberDistrictFormat | taxNumberNegativePattern
  | taxNumberCheckDigit
  | criminalFileFormat | criminalFileOffice | criminalFileCheckDigit
  deriving Repr, DecidableEq

namespace CustomFieldType

/-- The code a validation result carries. A consumer switches on this, not on the detail key. -/
def errorCode : CustomFieldType → String
  | .identificationNumber => "ungueltigeIDNummer"
  | .taxNumber => "ungueltigeSteuernummer"
  | .unitValueFileReference => "ungueltigesEinheitswertAktenzeichen"
  | .taxOfficeNumber => "ungueltigeBundesfinanzamtsnummer"
  | .countryAbbreviation => "ungueltigesLaenderkuerzel"
  | .iban => "ungueltigeIBAN"
  | .ibanInternational => "ungueltigeIBANinternational"
  | .bic => "ungueltigeBIC"
  | .bicInternational => "ungueltigerBICinternational"
  | .dateMonthYear => "ungueltigesDatumMMJJ"
  | .dateDayMonthYear => "ungueltigesDatumTTMMJJ"
  | .federalTaxNumber => "ungueltigeBundessteuernummer"
  | .criminalFileReference => "ungueltigesStrafAktenzeichen"

/-- The separate code the identification number surfaces for a value in the reserved test range. It is not any type's ordinary code, so a consumer enumerating `errorCode` alone misses it. -/
def testRangeCode : String := "testIDNummer"

/-- Every registered type. -/
def all : List CustomFieldType :=
  [.identificationNumber, .taxNumber, .unitValueFileReference,
    .taxOfficeNumber, .countryAbbreviation, .iban, .ibanInternational, .bic, .bicInternational,
    .dateMonthYear, .dateDayMonthYear, .federalTaxNumber, .criminalFileReference]

end CustomFieldType

namespace CustomFieldTypeDetail

/-- The exact catalog identity a consumer resolving a message would look up. -/
def catalogKey : CustomFieldTypeDetail → String
  | .noError => "KEIN_FEHLER"
  | .bicFormat => "BIC_FORMALER_FEHLER"
  | .bicCountryCode => "BIC_LAENDERCODE_FEHLER"
  | .bicInternationalFormat => "BICINTERNATIONAL_FORMALER_FEHLER"
  | .taxOfficeNumberFormat => "BUFANR_FORMALER_FEHLER"
  | .taxOfficeNumberInvalidOffice => "BUFANR_UNGUELTIGE_FINANZAMTSNR"
  | .federalTaxNumberInvalid => "BUNDESSTNR_UNGUELTIG"
  | .dateInvalid => "DATUM_UNGUELTIG"
  | .unitValueOffice => "EWAZ_FINANZAMT_FEHLER"
  | .unitValueFormat => "EWAZ_FORMALER_FEHLER"
  | .unitValueFormatKey => "EWAZ_FORMATSCHLUESSEL_FEHLER"
  | .unitValueCheckDigit => "EWAZ_PRUEFZIFFER_FEHLER"
  | .ibanFormat => "IBAN_FORMALER_FEHLER"
  | .ibanCountryCode => "IBAN_LAENDERCODE_FEHLER"
  | .ibanCountryFormat => "IBAN_LANDESFORMAT_FEHLER"
  | .ibanCheckDigit => "IBAN_PRUEFZIFFER_FEHLER"
  | .ibanWhitespace => "IBAN_LEERZEICHEN_UNGUELTIG"
  | .ibanInternationalFormat => "IBANINTERNATIONAL_FORMALER_FEHLER"
  | .ibanInternationalCountryFormat => "IBANINTERNATIONAL_LANDESFORMAT_FEHLER"
  | .ibanInternationalCheckDigit => "IBANINTERNATIONAL_PRUEFZIFFER_FEHLER"
  | .ibanInternationalWhitespace => "IBANINTERNATIONAL_LEERZEICHEN_UNGUELTIG"
  | .identificationNumberTestOnly => "IDNR_NUR_FUER_TEST"
  | .identificationNumberNotNumeric => "IDNR_NICHT_NUMERISCH"
  | .identificationNumberDigitSequence => "IDNR_ZIFFERNFOLGE_FEHLER"
  | .identificationNumberLength => "IDNR_LAENGE_UNGUELTIG"
  | .identificationNumberCheckDigit => "IDNR_PRUEFZIFFER_UNGUELTIG"
  | .identificationNumberWhitespace => "IDNR_LEERZEICHEN_UNGUELTIG"
  | .countryAbbreviationInvalid => "LAENDERKUERZEL_UNGUELTIG"
  | .taxNumberFormat => "STNR_FORMALER_FEHLER"
  | .taxNumberOffice => "STNR_FINANZAMT_FEHLER"
  | .taxNumberDistrictFormat => "STNR_FORMALER_FEHLER_BEZIRK"
  | .taxNumberNegativePattern => "STNR_FORMALER_NEGATIVMUSTER"
  | .taxNumberCheckDigit => "STNR_PRUEFZIFFER_FEHLER"
  | .criminalFileFormat => "STRAFAZ_FORMAT_FEHLER"
  | .criminalFileOffice => "STRAFAZ_FINANZAMT_FEHLER"
  | .criminalFileCheckDigit => "STRAFAZ_PRUEFZIFFER_FEHLER"

/-- The types whose validator can select this key. A list rather than a single type because the two date types share one key, and empty for the success sentinel, which belongs to every validator and refuses for none. -/
def owners : CustomFieldTypeDetail → List CustomFieldType
  | .noError => []
  | .bicFormat | .bicCountryCode => [.bic]
  | .bicInternationalFormat => [.bicInternational]
  | .taxOfficeNumberFormat | .taxOfficeNumberInvalidOffice => [.taxOfficeNumber]
  | .federalTaxNumberInvalid => [.federalTaxNumber]
  | .dateInvalid => [.dateMonthYear, .dateDayMonthYear]
  | .unitValueOffice | .unitValueFormat | .unitValueFormatKey | .unitValueCheckDigit =>
      [.unitValueFileReference]
  | .ibanFormat | .ibanCountryCode | .ibanCountryFormat | .ibanCheckDigit | .ibanWhitespace =>
      [.iban]
  | .ibanInternationalFormat | .ibanInternationalCountryFormat | .ibanInternationalCheckDigit
  | .ibanInternationalWhitespace => [.ibanInternational]
  | .identificationNumberTestOnly | .identificationNumberNotNumeric
  | .identificationNumberDigitSequence | .identificationNumberLength
  | .identificationNumberCheckDigit | .identificationNumberWhitespace =>
      [.identificationNumber]
  | .countryAbbreviationInvalid => [.countryAbbreviation]
  | .taxNumberFormat | .taxNumberOffice | .taxNumberDistrictFormat | .taxNumberNegativePattern
  | .taxNumberCheckDigit => [.taxNumber]
  | .criminalFileFormat | .criminalFileOffice | .criminalFileCheckDigit =>
      [.criminalFileReference]

/-- The code a refusal carrying this key surfaces, given the type whose validator produced it. Every key surfaces its type's own code except the reserved-test-range key, which is the whole reason this is a function of both arguments rather than of the type alone. -/
def surfacedCode (detail : CustomFieldTypeDetail) (owner : CustomFieldType) : String :=
  match detail with
  | .identificationNumberTestOnly => CustomFieldType.testRangeCode
  | _ => owner.errorCode

/-- Every detail key. -/
def all : List CustomFieldTypeDetail :=
  [.noError, .bicFormat, .bicCountryCode, .bicInternationalFormat, .taxOfficeNumberFormat,
    .taxOfficeNumberInvalidOffice, .federalTaxNumberInvalid, .dateInvalid, .unitValueOffice,
    .unitValueFormat, .unitValueFormatKey, .unitValueCheckDigit, .ibanFormat, .ibanCountryCode,
    .ibanCountryFormat, .ibanCheckDigit, .ibanWhitespace, .ibanInternationalFormat,
    .ibanInternationalCountryFormat, .ibanInternationalCheckDigit, .ibanInternationalWhitespace,
    .identificationNumberTestOnly, .identificationNumberNotNumeric,
    .identificationNumberDigitSequence, .identificationNumberLength,
    .identificationNumberCheckDigit, .identificationNumberWhitespace, .countryAbbreviationInvalid,
    .taxNumberFormat, .taxNumberOffice, .taxNumberDistrictFormat, .taxNumberNegativePattern,
    .taxNumberCheckDigit, .criminalFileFormat, .criminalFileOffice, .criminalFileCheckDigit]

/-- The keys a given type's validator can select, refusals only. -/
def refusalsOf (type : CustomFieldType) : List CustomFieldTypeDetail :=
  all.filter (fun detail => detail.owners.contains type)

end CustomFieldTypeDetail

end A12Kernel
