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
