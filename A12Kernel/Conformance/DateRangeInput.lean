import A12Kernel.Elaboration.DateRangeBound

/-! # Checked DateRange stored-text ingestion, direct-bound, comparison, and numeric-component locks -/

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

private def leapDay2024 : DateRangeValue := {
  start := dateValue 1709164800000 2024 2 29
  finish := dateValue 1709164800000 2024 2 29
}

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

/- Unsupported declaration and zone profiles are explicit ingestion insufficiency, not semantic invalidity. -/
example :
    (match classifyStoredDateRange "UTC"
        { format := "yyyy-MM-dd", separator := "-" }
        "2024-01-01-2024-01-31" with
      | .error (.unsupportedPolicy format separator) =>
          format == "yyyy-MM-dd" && separator == "-"
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

private def dottedTravel : FlatFieldDecl := {
  travel with
  dateRangePolicy := some dottedPolicy
}

private def dottedModel : FlatModel := {
  fields := [dottedTravel]
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

private def dottedPrepared :
    PreparedFlatStringContext dottedModel builtinStringPatternCompiler :=
  (prepareFlatStringContext { now := { epochMillis := 0 } }
    builtinStringPatternCompiler dottedModel).toOption.get (by native_decide)

private def checkDottedOne (stored : String) (raw : RawCell) :=
  checkDocument dottedPrepared "en_US" {
    instantiatedRows := []
    cells := [{
      address := { field := dottedTravel.id, path := [] }
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

private def unsupportedPolicyTravel : FlatFieldDecl := {
  travel with
  dateRangePolicy := some { format := "yyyy-MM-dd", separator := "-" }
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

/- Canonical coherence covers both yearless and Base-Year-resolved fragment cells through the same immutable checked document. -/
example :
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

/- Both checked policies select their exact stored endpoints instead of reconstructing them from rendered text. -/
example :
    let isoInput := (checkOne "2024-01-01/2024-01-31"
      (.parsed (.dateRange january))).toOption.get (by native_decide)
    let dottedInput := (checkDottedOne "01.01.2024-31.01.2024"
      (.parsed (.dateRange january))).toOption.get (by native_decide)
    let start := (elaborateDateRangeBound model travel.id .start).toOption.get
      (by native_decide)
    let finish := (elaborateDateRangeBound dottedModel dottedTravel.id .finish).toOption.get
      (by native_decide)
    (match start.evaluate .validation isoInput with
      | .ok (.value selected) => selected == january.start
      | _ => false) &&
    (match finish.evaluate .validation dottedInput with
      | .ok (.value selected) => selected == january.finish
      | _ => false) = true := by
  native_decide

/- Endpoint projection preserves every part of the shared `DateValue`, including identities a rendered label cannot carry. -/
example :
    let altered : DateRangeValue := {
      january with
      start := {
        january.start with
        instant := { epochMillis := january.start.instant.epochMillis + 1 }
        basis := .legacyHybrid } }
    altered.select .start == altered.start &&
      altered.select .finish == altered.finish &&
      altered.select .start != january.start := by
  native_decide

/- Empty, validation-unknown, and computation-poison remain distinct through the same checked field query. -/
example :
    let bound := (elaborateDateRangeBound model travel.id .start).toOption.get
      (by native_decide)
    let empty := (checkOne "" .presentEmpty).toOption.get (by native_decide)
    let invalid := (checkOne "garbage"
      (.rejected .dateRangeSeparator)).toOption.get (by native_decide)
    (match bound.evaluate .validation empty with
      | .ok .empty => true
      | _ => false) &&
    (match bound.evaluate .validation invalid with
      | .ok (.unknown .dateRangeSeparator) => true
      | _ => false) &&
    (match bound.evaluate .computation invalid with
      | .ok (.poison .dateRangeSeparator) => true
      | _ => false) = true := by
  native_decide

/- Admission stays bounded to direct nonrepeatable DateRange fields under the two canonical policies. -/
example :
    let repeated : FlatFieldDecl := {
      travel with
      groupPath := ["Order", "Rows"]
      repeatableScope := [10] }
    let repeatedModel : FlatModel := {
      fields := [repeated]
      repeatableGroups := [{ level := 10, path := ["Order", "Rows"] }] }
    let dateField : FlatFieldDecl := {
      id := 2
      groupPath := ["Order"]
      name := "Date"
      policy := { kind := .temporal .date TemporalComponents.fullDate }
      temporalTargetPolicy := some {
        format := "yyyy-MM-dd"
        partialMode := .full } }
    let dateModel : FlatModel := { fields := [dateField] }
    (elaborateDateRangeBound model travel.id .start).isOk &&
      (elaborateDateRangeBound dottedModel dottedTravel.id .finish).isOk &&
      (match elaborateDateRangeBound monthModel monthTravel.id .start with
        | .error (.unsupportedPolicy field format separator) =>
            field == monthTravel.id && format == "MM" && separator == "/"
        | _ => false) &&
      (match elaborateDateRangeBound unsupportedPolicyModel
          unsupportedPolicyTravel.id .start with
        | .error (.unsupportedPolicy field format separator) =>
            field == unsupportedPolicyTravel.id &&
              format == "yyyy-MM-dd" && separator == "-"
        | _ => false) &&
      (match elaborateDateRangeBound repeatedModel repeated.id .start with
        | .error (.source (.repeatableReference path)) =>
            path == repeated.path
        | _ => false) &&
      (match elaborateDateRangeBound dateModel dateField.id .start with
        | .error (.sourceNotDateRange field (.temporal .date)) =>
            field == dateField.id
        | _ => false) = true := by
  native_decide

private def fullDate (year : Int) (month day : Nat)
    (admitted : (FullDate.ofYmd? year month day).isSome) : FullDate :=
  (FullDate.ofYmd? year month day).get admitted

private def januaryMidpoint : FullDate :=
  fullDate 2024 1 15 (by native_decide)

/- Start and finish retain their authored identity while delegating to the existing full-Date comparison. -/
example :
    let input := (checkOne "2024-01-01/2024-01-31"
      (.parsed (.dateRange january))).toOption.get (by native_decide)
    let start := (elaborateDateRangeBoundComparison model travel.id .start
      .left .before januaryMidpoint).toOption.get (by native_decide)
    let finish := (elaborateDateRangeBoundComparison model travel.id .finish
      .left .before januaryMidpoint).toOption.get (by native_decide)
    (start.evaluate input).toOption = some {
      selected := .value january.start
      verdict := .fired .value
    } ∧
    (finish.evaluate input).toOption = some {
      selected := .value january.finish
      verdict := .notFired
    } := by
  native_decide

/- Authored operand position remains observable for directional comparisons. -/
example :
    let selected := (elaborateDateRangeBoundComparison model travel.id .start
      .right .before januaryMidpoint).toOption.get (by native_decide)
    (selected.evaluateSelected (.value january.start)).toOption = some {
      selected := .value january.start
      verdict := .notFired
    } := by
  native_decide

/- Empty and formal unavailability retain both their selected observation and established validation verdict. -/
example :
    let comparison := (elaborateDateRangeBoundComparison model travel.id .start
      .left .equal januaryMidpoint).toOption.get (by native_decide)
    let empty := (checkOne "" .presentEmpty).toOption.get (by native_decide)
    let invalid := (checkOne "garbage"
      (.rejected .dateRangeSeparator)).toOption.get (by native_decide)
    (comparison.evaluate empty).toOption = some {
      selected := .empty
      verdict := .notFired
    } ∧
    (comparison.evaluate invalid).toOption = some {
      selected := .unknown .dateRangeSeparator
      verdict := .unknown
    } := by
  native_decide

/- Comparison projects decoded calendar identity while preserving the exact selected endpoint for explanation. -/
example :
    let comparison := (elaborateDateRangeBoundComparison model travel.id .start
      .left .before januaryMidpoint).toOption.get (by native_decide)
    let altered : DateValue := {
      january.start with
      instant := { epochMillis := january.start.instant.epochMillis + 1 }
      basis := .legacyHybrid }
    (comparison.evaluateSelected (.value altered)).toOption = some {
      selected := .value altered
      verdict := .fired .value
    } := by
  native_decide

/- A malformed universal payload cannot be silently coerced into the full-Date comparison domain. -/
example :
    let comparison := (elaborateDateRangeBoundComparison model travel.id .start
      .left .equal januaryMidpoint).toOption.get (by native_decide)
    let malformed : DateValue := {
      january.start with
      parts := { year := 2024, month := 1, day := 0 } }
    (match comparison.evaluateSelected (.value malformed) with
      | .error (.selectedDateUnavailable source value) =>
          source == travel.id && value == malformed
      | _ => false) = true := by
  native_decide

/- All four component tags compose with the checked bound while retaining start/finish identity. -/
example :
    let stored := "2019-11-30/2024-04-01"
    let raw := (classifyStoredDateRange "UTC" isoPolicy stored).toOption.get
      (by native_decide)
    let input := (checkOne stored raw).toOption.get (by native_decide)
    let startYear := (elaborateDateRangeBoundComponent model travel.id .start
      .year).toOption.get (by native_decide)
    let finishMonth := (elaborateDateRangeBoundComponent model travel.id .finish
      .month).toOption.get (by native_decide)
    let startDay := (elaborateDateRangeBoundComponent model travel.id .start
      .day).toOption.get (by native_decide)
    let finishQuarter :=
      (elaborateDateRangeBoundComponent model travel.id .finish
        .quarter).toOption.get (by native_decide)
    (startYear.evaluate input).toOption.map (·.component) =
        some (.value 2019 .fixed) ∧
      (finishMonth.evaluate input).toOption.map (·.component) =
        some (.value 4 .fixed) ∧
      (startDay.evaluate input).toOption.map (·.component) =
        some (.value 30 .fixed) ∧
      (finishQuarter.evaluate input).toOption.map (·.component) =
        some (.value 2 .fixed) := by
  native_decide

/- Component extraction retains exact selected identity, fillable empty zero, and formal cause. -/
example :
    let component := (elaborateDateRangeBoundComponent model travel.id .start
      .year).toOption.get (by native_decide)
    let altered : DateValue := {
      january.start with
      instant := { epochMillis := january.start.instant.epochMillis + 1 }
      basis := .legacyHybrid }
    let empty := (checkOne "" .presentEmpty).toOption.get (by native_decide)
    let invalid := (checkOne "garbage"
      (.rejected .dateRangeSeparator)).toOption.get (by native_decide)
    component.evaluateSelected (.value altered) = {
      selected := .value altered
      component := .value 2024 .fixed
    } ∧
    (component.evaluate empty).toOption = some {
      selected := .empty
      component := .value 0 .both
    } ∧
    (component.evaluate invalid).toOption = some {
      selected := .unknown .dateRangeSeparator
      component := .unknown .dateRangeSeparator
    } := by
  native_decide

end A12Kernel.Conformance.DateRangeInput
