import A12Kernel.Elaboration.CheckedDocument

/-! # Checked DateRange stored-text ingestion locks -/

namespace A12Kernel.Conformance.DateRangeInput

open A12Kernel

private def isoPolicy : DateRangeDeclarationPolicy := {
  format := "yyyy-MM-dd"
  separator := "/"
}

private def dottedPolicy : DateRangeDeclarationPolicy := {
  format := "dd.MM.yyyy"
  separator := "-"
}

private def monthPolicy : DateRangeDeclarationPolicy := {
  format := "MM"
  separator := "/"
}

private def monthDayPolicy : DateRangeDeclarationPolicy := {
  format := "MM-dd"
  separator := "/"
}

private def yearPolicy : DateRangeDeclarationPolicy := {
  format := "yyyy"
  separator := "/"
}

private def yearMonthPolicy : DateRangeDeclarationPolicy := {
  format := "yyyy-MM"
  separator := "/"
}

private def dateValue (epochMillis : Int) (year month day : Nat) : DateValue := {
  instant := { epochMillis }
  parts := { year, month, day }
  basis := .storedGregorian
}

private def january : DateRangeValue := {
  start := dateValue 1704067200000 2024 1 1
  finish := dateValue 1706659200000 2024 1 31
}

private def berlinTransition : DateRangeValue := {
  start := dateValue 1711839600000 2024 3 31
  finish := dateValue 1711922400000 2024 4 1
}

private def oneDay : DateRangeValue := {
  start := dateValue 1717200000000 2024 6 1
  finish := dateValue 1717200000000 2024 6 1
}

private def gregorianFloorRange : DateRangeValue := {
  start := dateValue (-12187670400000) 1583 10 16
  finish := dateValue (-12187670400000) 1583 10 16
}

private def february2024 : DateRangeValue := {
  start := dateValue 1706745600000 2024 2 1
  finish := dateValue 1709164800000 2024 2 29
}

private def february2023 : DateRangeValue := {
  start := dateValue 1675209600000 2023 2 1
  finish := dateValue 1677542400000 2023 2 28
}

private def leapDay2024 : DateRangeValue := {
  start := dateValue 1709164800000 2024 2 29
  finish := dateValue 1709164800000 2024 2 29
}

private def years2024To2025 : DateRangeValue := {
  start := dateValue 1704067200000 2024 1 1
  finish := dateValue 1767139200000 2025 12 31
}

/- A stored `yyyy` range completes its start and finish asymmetrically before exact zone resolution. -/
example :
    (classifyStoredDateRangeForModel "UTC" none yearPolicy
      "2024/2025").toOption =
      some (.parsed (.dateRange (.exact years2024To2025))) ∧
    (classifyStoredDateRangeForModel "UTC" (some 1900) yearPolicy
      "2024/2025").toOption =
      some (.parsed (.dateRange (.exact years2024To2025))) ∧
    (classifyStoredDateRangeForModel "UTC" none yearPolicy "").toOption =
      some .presentEmpty := by
  native_decide

/- A stored `yyyy-MM` range completes the finish to the calendar's leap-aware last day without consulting Base Year. -/
example :
    (classifyStoredDateRangeForModel "UTC" none yearMonthPolicy
      "2024-02/2024-02").toOption =
      some (.parsed (.dateRange (.exact february2024))) ∧
    (classifyStoredDateRangeForModel "UTC" (some 1900) yearMonthPolicy
      "2023-02/2023-02").toOption =
      some (.parsed (.dateRange (.exact february2023))) ∧
    (classifyStoredDateRangeForModel "UTC" none yearMonthPolicy "").toOption =
      some .presentEmpty := by
  native_decide

/- Stored `yyyy-MM` parsing preserves separator, width, calendar, order, and Gregorian-floor causes. -/
example :
    (classifyStoredDateRangeForModel "UTC" none yearMonthPolicy
      "2024-02").toOption = some (.rejected .dateRangeSeparator) ∧
    (classifyStoredDateRangeForModel "UTC" none yearMonthPolicy
      "2024-2/2024-02").toOption = some (.rejected .dateRangeFormat) ∧
    (classifyStoredDateRangeForModel "UTC" none yearMonthPolicy
      "2024-13/2024-13").toOption = some (.rejected .dateRangeFormat) ∧
    (classifyStoredDateRangeForModel "UTC" none yearMonthPolicy
      "2024-03/2024-02").toOption = some (.rejected .dateRangeInvalid) ∧
    (classifyStoredDateRangeForModel "UTC" none yearMonthPolicy
      "1582-12/1583-01").toOption = some (.rejected .dateRangeTooEarly) := by
  native_decide

/- Stored `yyyy` parsing preserves separator, width, order, and Gregorian-floor causes. -/
example :
    (classifyStoredDateRangeForModel "UTC" none yearPolicy "2024").toOption =
      some (.rejected .dateRangeSeparator) ∧
    (classifyStoredDateRangeForModel "UTC" none yearPolicy
      "2024/02025").toOption = some (.rejected .dateRangeFormat) ∧
    (classifyStoredDateRangeForModel "UTC" none yearPolicy
      "2025/2024").toOption = some (.rejected .dateRangeInvalid) ∧
    (classifyStoredDateRangeForModel "UTC" none yearPolicy
      "1582/1583").toOption = some (.rejected .dateRangeTooEarly) := by
  native_decide

/- Yearless fragment ranges retain only their measured component identities, while a declared Base Year resolves the same labels to the existing exact range carrier. -/
example :
    (classifyStoredDateRangeForModel "UTC" none monthPolicy "02/03").toOption =
      some (.parsed (.dateRange (.yearlessMonth 2 3))) ∧
    (classifyStoredDateRangeForModel "UTC" none monthDayPolicy
        "02-28/02-29").toOption =
      some (.parsed (.dateRange (.yearlessMonthDay
        { month := 2, day := 28 } { month := 2, day := 29 }))) ∧
    (classifyStoredDateRangeForModel "UTC" (some 2024) monthPolicy
        "02/02").toOption =
      some (.parsed (.dateRange february2024)) ∧
    (classifyStoredDateRangeForModel "UTC" (some 2024) monthDayPolicy
        "02-29/02-29").toOption =
      some (.parsed (.dateRange leapDay2024)) := by
  native_decide

/- Fragment parsing retains the established separator, format, and ordering causes without fabricating a year. -/
example :
    (classifyStoredDateRangeForModel "UTC" none monthPolicy "02").toOption =
      some (.rejected .dateRangeSeparator) ∧
    (classifyStoredDateRangeForModel "UTC" none monthDayPolicy
        "02-30/03-01").toOption =
      some (.rejected .dateRangeFormat) ∧
    (classifyStoredDateRangeForModel "UTC" none monthPolicy "12/01").toOption =
      some (.rejected .dateRangeInvalid) ∧
    (classifyStoredDateRangeForModel "UTC" none monthDayPolicy
        "03-01/02-29").toOption =
      some (.rejected .dateRangeInvalid) := by
  native_decide

/- Both exact declaration pairs decode to typed endpoint values rather than preserving only the stored token. -/
example :
    (classifyStoredDateRange "UTC" isoPolicy
        "2024-01-01/2024-01-31").toOption =
      some (.parsed (.dateRange january)) ∧
    (classifyStoredDateRange "UTC" dottedPolicy
        "01.01.2024-31.01.2024").toOption =
      some (.parsed (.dateRange january)) ∧
    (classifyStoredDateRange "UTC" isoPolicy
        "2024-06-01/2024-06-01").toOption =
      some (.parsed (.dateRange oneDay)) ∧
    (classifyStoredDateRange "UTC" isoPolicy
        "1583-10-16/1583-10-16").toOption =
      some (.parsed (.dateRange gregorianFloorRange)) := by
  native_decide

/- The model zone supplies exact endpoint identity independently of the decoded labels. -/
example :
    (classifyStoredDateRange "Europe/Berlin" dottedPolicy
        "31.03.2024-01.04.2024").toOption =
      some (.parsed (.dateRange berlinTransition)) := by
  native_decide

/- Empty placement and the four externally distinct formal failures do not collapse. Ordering precedes the floor. -/
example :
    (classifyStoredDateRange "UTC" isoPolicy "").toOption =
      some .presentEmpty ∧
    (classifyStoredDateRange "UTC" isoPolicy "garbage").toOption =
      some (.rejected .dateRangeSeparator) ∧
    (classifyStoredDateRange "UTC" dottedPolicy
        "01.01.2024/31.01.2024").toOption =
      some (.rejected .dateRangeSeparator) ∧
    (classifyStoredDateRange "UTC" isoPolicy
        "2024-01-01/2024-01-31/2024-02-01").toOption =
      some (.rejected .dateRangeFormat) ∧
    (classifyStoredDateRange "UTC" isoPolicy
        "/2024-01-31").toOption =
      some (.rejected .dateRangeFormat) ∧
    (classifyStoredDateRange "UTC" isoPolicy
        "2024-01-01/").toOption =
      some (.rejected .dateRangeFormat) ∧
    (classifyStoredDateRange "UTC" isoPolicy
        "2024-01-01/not-a-date").toOption =
      some (.rejected .dateRangeFormat) ∧
    (classifyStoredDateRange "UTC" isoPolicy
        "2024-02-31/2024-06-30").toOption =
      some (.rejected .dateRangeFormat) ∧
    (classifyStoredDateRange "UTC" dottedPolicy
        "1.1.2024-31.01.2024").toOption =
      some (.rejected .dateRangeFormat) ∧
    (classifyStoredDateRange "UTC" isoPolicy
        "٢٠٢٤-01-01/2024-01-31").toOption =
      some (.rejected .dateRangeFormat) ∧
    (classifyStoredDateRange "UTC" isoPolicy
        "2024-06-30/2024-06-01").toOption =
      some (.rejected .dateRangeInvalid) ∧
    (classifyStoredDateRange "UTC" isoPolicy
        "1583-10-15/1583-10-16").toOption =
      some (.rejected .dateRangeTooEarly) ∧
    (classifyStoredDateRange "UTC" isoPolicy
        "1583-10-17/1583-10-15").toOption =
      some (.rejected .dateRangeInvalid) := by
  native_decide

/- Each retained cause exposes the exact fixed runtime code measured by the external formal-check route. -/
example :
    FormalCause.dateRangeSeparator.fixedFormalErrorCode? =
      some "datumBereichTrennerFehlt" ∧
    FormalCause.dateRangeFormat.fixedFormalErrorCode? =
      some "datumBereichFormatFalsch" ∧
    FormalCause.dateRangeInvalid.fixedFormalErrorCode? =
      some "datumBereichNichtGueltig" ∧
    FormalCause.dateRangeTooEarly.fixedFormalErrorCode? =
      some "datumBereichDatumFalsch" := by
  decide

/- The two pairs the Kernel allowlist adds beyond the checked stored-input profiles are legal declarations without an input profile: declaration legality and local ingestion support are separate decisions. -/
example :
    let monthEmptySeparator : DateRangeDeclarationPolicy :=
      { format := "MM", separator := "" }
    let dottedDayMonth : DateRangeDeclarationPolicy :=
      { format := "dd.MM", separator := "-" }
    (monthEmptySeparator.error?, dottedDayMonth.error?) = (none, none) ∧
      (DateRangeInputFormat.ofPolicy? monthEmptySeparator,
        DateRangeInputFormat.ofPolicy? dottedDayMonth) = (none, none) := by
  native_decide

/- Unsupported declaration and zone profiles are explicit ingestion insufficiency, not semantic invalidity. -/
example :
    (match classifyStoredDateRange "UTC"
        { format := "dd.MM", separator := "-" }
        "01.06-30.09" with
      | .error (.unsupportedPolicy format separator) =>
          format == "dd.MM" && separator == "-"
      | _ => false) = true ∧
    (match classifyStoredDateRange "Pacific/Apia" isoPolicy
        "2024-01-01/2024-01-31" with
      | .error (.unsupportedZone zoneId) => zoneId == "Pacific/Apia"
      | _ => false) = true := by
  native_decide

private def travel : FlatFieldDecl := {
  id := 1
  groupPath := ["Order"]
  name := "Travel"
  policy := { kind := .dateRange }
  dateRangePolicy := some isoPolicy
}

private def model : FlatModel := {
  fields := [travel]
  timeZoneId := "UTC"
}

private def monthTravel : FlatFieldDecl := {
  travel with
  name := "Months"
  dateRangePolicy := some monthPolicy
}

private def monthModel : FlatModel := {
  fields := [monthTravel]
  timeZoneId := "UTC"
}

private def baseYearMonthModel : FlatModel := {
  monthModel with baseYear := some 2024
}

private def yearTravel : FlatFieldDecl := {
  travel with
  name := "Years"
  dateRangePolicy := some yearPolicy
}

private def yearModel : FlatModel := {
  fields := [yearTravel]
  timeZoneId := "UTC"
}

private def yearMonthTravel : FlatFieldDecl := {
  travel with
  name := "YearMonths"
  dateRangePolicy := some yearMonthPolicy
}

private def yearMonthModel : FlatModel := {
  fields := [yearMonthTravel]
  timeZoneId := "UTC"
}

private def prepared :
    PreparedFlatStringContext model builtinStringPatternCompiler :=
  (prepareFlatStringContext { now := { epochMillis := 0 } }
    builtinStringPatternCompiler model).toOption.get (by native_decide)

private def checkOne (stored : String) (raw : RawCell) :=
  checkDocument prepared "en_US" {
    instantiatedRows := []
    cells := [{
      address := { field := travel.id, path := [] }
      stored
      raw
    }]
  }

private def monthPrepared :
    PreparedFlatStringContext monthModel builtinStringPatternCompiler :=
  (prepareFlatStringContext { now := { epochMillis := 0 } }
    builtinStringPatternCompiler monthModel).toOption.get (by native_decide)

private def checkMonthOne (stored : String) (raw : RawCell) :=
  checkDocument monthPrepared "en_US" {
    instantiatedRows := []
    cells := [{
      address := { field := monthTravel.id, path := [] }
      stored
      raw
    }]
  }

private def baseYearMonthPrepared :
    PreparedFlatStringContext baseYearMonthModel builtinStringPatternCompiler :=
  (prepareFlatStringContext { now := { epochMillis := 0 } }
    builtinStringPatternCompiler baseYearMonthModel).toOption.get
      (by native_decide)

private def checkBaseYearMonthOne (stored : String) (raw : RawCell) :=
  checkDocument baseYearMonthPrepared "en_US" {
    instantiatedRows := []
    cells := [{
      address := { field := monthTravel.id, path := [] }
      stored
      raw
    }]
  }

private def yearPrepared :
    PreparedFlatStringContext yearModel builtinStringPatternCompiler :=
  (prepareFlatStringContext { now := { epochMillis := 0 } }
    builtinStringPatternCompiler yearModel).toOption.get (by native_decide)

private def checkYearOne (stored : String) (raw : RawCell) :=
  checkDocument yearPrepared "en_US" {
    instantiatedRows := []
    cells := [{
      address := { field := yearTravel.id, path := [] }
      stored
      raw
    }]
  }

private def yearMonthPrepared :
    PreparedFlatStringContext yearMonthModel builtinStringPatternCompiler :=
  (prepareFlatStringContext { now := { epochMillis := 0 } }
    builtinStringPatternCompiler yearMonthModel).toOption.get (by native_decide)

private def checkYearMonthOne (stored : String) (raw : RawCell) :=
  checkDocument yearMonthPrepared "en_US" {
    instantiatedRows := []
    cells := [{
      address := { field := yearMonthTravel.id, path := [] }
      stored
      raw
    }]
  }

private def unsupportedPolicyTravel : FlatFieldDecl := {
  travel with
  dateRangePolicy := some { format := "dd.MM", separator := "-" }
}

private def unsupportedPolicyModel : FlatModel := {
  fields := [unsupportedPolicyTravel]
  timeZoneId := "UTC"
}

private def unsupportedPolicyPrepared :
    PreparedFlatStringContext unsupportedPolicyModel
      builtinStringPatternCompiler :=
  (prepareFlatStringContext { now := { epochMillis := 0 } }
    builtinStringPatternCompiler unsupportedPolicyModel).toOption.get
      (by native_decide)

private def unsupportedZoneModel : FlatModel := {
  fields := [travel]
  timeZoneId := "Pacific/Apia"
}

private def unsupportedZonePrepared :
    PreparedFlatStringContext unsupportedZoneModel
      builtinStringPatternCompiler :=
  (prepareFlatStringContext { now := { epochMillis := 0 } }
    builtinStringPatternCompiler unsupportedZoneModel).toOption.get
      (by native_decide)

/- The single immutable document route accepts the canonical classification and rejects a caller-spoofed typed range. -/
example :
    (checkOne "2024-01-01/2024-01-31"
      (.parsed (.dateRange january))).toOption.map
        (fun checked => checked.flatContext.observeValidationAt travel.id) =
      some (.value (.dateRange january)) ∧
    (match checkOne "2024-01-01/2024-01-31"
        (.parsed (.dateRange berlinTransition)) with
      | .error (.incoherentCell address) =>
          address == { field := travel.id, path := [] }
      | _ => false) = true := by
  native_decide

/- Canonical coherence covers year-bearing, yearless, and Base-Year-resolved fragment cells through the same immutable checked document. -/
example :
    (checkYearOne "2024/2025"
      (.parsed (.dateRange (.exact years2024To2025)))).toOption.map
        (fun checked => checked.flatContext.observeValidationAt yearTravel.id) =
      some (.value (.dateRange (.exact years2024To2025))) ∧
    (match checkYearOne "2024/2025"
        (.parsed (.dateRange (.exact january))) with
      | .error (.incoherentCell address) =>
          address == { field := yearTravel.id, path := [] }
      | _ => false) = true ∧
    (checkYearMonthOne "2024-02/2024-02"
      (.parsed (.dateRange (.exact february2024)))).toOption.map
        (fun checked => checked.flatContext.observeValidationAt yearMonthTravel.id) =
      some (.value (.dateRange (.exact february2024))) ∧
    (match checkYearMonthOne "2024-02/2024-02"
        (.parsed (.dateRange (.exact february2023))) with
      | .error (.incoherentCell address) =>
          address == { field := yearMonthTravel.id, path := [] }
      | _ => false) = true ∧
    (checkMonthOne "02/03"
      (.parsed (.dateRange (.yearlessMonth 2 3)))).toOption.map
        (fun checked => checked.flatContext.observeValidationAt monthTravel.id) =
      some (.value (.dateRange (.yearlessMonth 2 3))) ∧
    (match checkMonthOne "02/03"
        (.parsed (.dateRange (.yearlessMonth 2 4))) with
      | .error (.incoherentCell address) =>
          address == { field := monthTravel.id, path := [] }
      | _ => false) = true ∧
    (checkBaseYearMonthOne "02/02"
      (.parsed (.dateRange february2024))).isOk = true ∧
    (match checkBaseYearMonthOne "02/02"
        (.parsed (.dateRange (.yearlessMonth 2 2))) with
      | .error (.incoherentCell address) =>
          address == { field := monthTravel.id, path := [] }
      | _ => false) = true := by
  native_decide

/- Wider policies retain the prior caller-classified boundary, while a filled value under a supported policy and unsupported zone fails canonical coherence. -/
example :
    (checkDocument unsupportedPolicyPrepared "en_US" {
      instantiatedRows := []
      cells := [{
        address := { field := unsupportedPolicyTravel.id, path := [] }
        stored := "caller-classified"
        raw := .parsed (.dateRange january)
      }]
    }).isOk = true ∧
    (match checkDocument unsupportedZonePrepared "en_US" {
      instantiatedRows := []
      cells := [{
        address := { field := travel.id, path := [] }
        stored := "2024-01-01/2024-01-31"
        raw := .parsed (.dateRange january)
      }]
    } with
      | .error (.incoherentCell address) =>
          address == { field := travel.id, path := [] }
      | _ => false) = true := by
  native_decide

/- Exact DateRange formal causes survive checked-document validation and computation reads. -/
example :
    ((checkOne "garbage" (.rejected .dateRangeSeparator)).toOption.bind
      fun checked =>
        (checked.read { field := travel.id, path := [] }).toOption.map
          fun cell =>
            (observeCell .validation cell,
              observeCell .computation cell)) =
      some (.unknown .dateRangeSeparator, .poison .dateRangeSeparator) ∧
    (match checkOne "garbage" (.rejected .malformed) with
      | .error (.incoherentCell address) =>
          address == { field := travel.id, path := [] }
      | _ => false) = true := by
  native_decide

end A12Kernel.Conformance.DateRangeInput
