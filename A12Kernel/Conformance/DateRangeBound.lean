import A12Kernel.Elaboration.DateRangeBound

/-! # Checked direct DateRange bound, comparison, and numeric-component locks -/

namespace A12Kernel.Conformance.DateRangeBound

open A12Kernel

private def policy (format separator : String) : DateRangeDeclarationPolicy := {
  format
  separator
}

private def field (declarationPolicy : DateRangeDeclarationPolicy) : FlatFieldDecl := {
  id := 1
  groupPath := ["Order"]
  name := "Travel"
  policy := { kind := .dateRange }
  dateRangePolicy := some declarationPolicy
}

private def modelFor (source : FlatFieldDecl) : FlatModel := {
  fields := [source]
  timeZoneId := "UTC"
}

private def isoPolicy := policy "yyyy-MM-dd" "/"
private def dottedPolicy := policy "dd.MM.yyyy" "-"
private def monthPolicy := policy "MM" "/"
private def monthDayPolicy := policy "MM-dd" "/"
private def yearPolicy := policy "yyyy" "/"
private def yearMonthPolicy := policy "yyyy-MM" "/"
private def travel := field isoPolicy
private def dottedTravel := field dottedPolicy
private def monthTravel := field monthPolicy
private def monthDayTravel := field monthDayPolicy
private def yearTravel := field yearPolicy
private def yearMonthTravel := field yearMonthPolicy
private def model := modelFor travel
private def dottedModel := modelFor dottedTravel
private def monthModel := modelFor monthTravel
private def monthDayModel := modelFor monthDayTravel
private def yearModel := modelFor yearTravel
private def yearMonthModel := modelFor yearMonthTravel

private def configuredMonthModel (baseYear : Int) : FlatModel := {
  monthModel with baseYear := some baseYear
}

private def configuredMonthDayModel (baseYear : Int) : FlatModel := {
  monthDayModel with baseYear := some baseYear
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

private def year2024 : DateRangeValue := {
  start := dateValue 1704067200000 2024 1 1
  finish := dateValue 1735603200000 2024 12 31
}

private def february2024 : DateRangeValue := {
  start := dateValue 1706745600000 2024 2 1
  finish := dateValue 1709164800000 2024 2 29
}

private def february2023 : DateRangeValue := {
  start := dateValue 1675209600000 2023 2 1
  finish := dateValue 1677542400000 2023 2 28
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
    builtinStringPatternCompiler yearMonthModel).toOption.get
      (by native_decide)

private def checkYearMonthOne (stored : String) (raw : RawCell) :=
  checkDocument yearMonthPrepared "en_US" {
    instantiatedRows := []
    cells := [{
      address := { field := yearMonthTravel.id, path := [] }
      stored
      raw
    }]
  }

/- Both canonical checked policies select their exact stored endpoints instead of reconstructing them from rendered text. -/
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

private def fullDate (year : Int) (month day : Nat)
    (admitted : (FullDate.ofYmd? year month day).isSome) : FullDate :=
  (FullDate.ofYmd? year month day).get admitted

/- Admission accepts the exact-valued year-bearing profiles, while yearless and addressing boundaries stay refused. -/
example :
    let unsupportedPolicyTravel := field (policy "yyyy-MM-dd" "-")
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
      (elaborateDateRangeBound yearModel yearTravel.id .start).isOk &&
      (elaborateDateRangeBound yearMonthModel yearMonthTravel.id .finish).isOk &&
      (elaborateDateRangeBound (configuredMonthModel 2024) monthTravel.id
        .start).isOk &&
      (match elaborateDateRangeBound monthModel monthTravel.id .start with
        | .error (.unsupportedPolicy source format separator) =>
            source == monthTravel.id && format == "MM" && separator == "/"
        | _ => false) &&
      (match elaborateDateRangeBound monthDayModel monthDayTravel.id .start with
        | .error (.unsupportedPolicy source format separator) =>
            source == monthDayTravel.id && format == "MM-dd" &&
              separator == "/"
        | _ => false) &&
      (match elaborateDateRangeBound (configuredMonthDayModel 2024)
          monthDayTravel.id .start with
        | .error (.unsupportedPolicy source format separator) =>
            source == monthDayTravel.id && format == "MM-dd" &&
              separator == "/"
        | _ => false) &&
      (match elaborateDateRangeBound (modelFor unsupportedPolicyTravel)
          unsupportedPolicyTravel.id .start with
        | .error (.unsupportedPolicy source format separator) =>
            source == unsupportedPolicyTravel.id &&
              format == "yyyy-MM-dd" && separator == "-"
        | _ => false) &&
      (match elaborateDateRangeBound repeatedModel repeated.id .start with
        | .error (.source (.repeatableReference path)) =>
            path == repeated.path
        | _ => false) &&
      (match elaborateDateRangeBound dateModel dateField.id .start with
        | .error (.sourceNotDateRange source (.temporal .date)) =>
            source == dateField.id
        | _ => false) = true := by
  native_decide

private def yearBoundConsumerSnapshot : Option
    (CellObservation DateValue × CellObservation DateValue ×
      DateRangeBoundComparisonResult × DateRangeBoundComponentResult) := do
  let input ← (checkYearOne "2024/2024"
    (.parsed (.dateRange (.exact year2024)))).toOption
  let januarySecond := fullDate 2024 1 2 (by native_decide)
  let start ← (elaborateDateRangeBound yearModel yearTravel.id .start).toOption
  let finish ← (elaborateDateRangeBound yearModel yearTravel.id .finish).toOption
  let comparison ← (elaborateDateRangeBoundComparison yearModel yearTravel.id
    .start .left .before januarySecond).toOption
  let component ← (elaborateDateRangeBoundComponent yearModel yearTravel.id
    .finish .quarter).toOption
  let startValue ← (start.evaluate .validation input).toOption
  let finishValue ← (finish.evaluate .validation input).toOption
  let comparisonResult ← (comparison.evaluate input).toOption
  let componentResult ← (component.evaluate input).toOption
  pure (startValue, finishValue, comparisonResult, componentResult)

/- The year fragment preserves both exact stored endpoints and composes with the existing full-Date comparison and numeric component consumers. -/
example : yearBoundConsumerSnapshot = some (
    .value year2024.start,
    .value year2024.finish,
    {
      selected := .value year2024.start
      verdict := .fired .value
    },
    {
      selected := .value year2024.finish
      component := .value 4 .fixed
    }) := by
  native_decide

private def yearMonthBoundConsumerSnapshot (range : DateRangeValue)
    (stored : String) (februaryTwentyEighth : FullDate) : Option
      (CellObservation DateValue × CellObservation DateValue ×
        Verdict × NumericOperand) := do
  let input ← (checkYearMonthOne stored
    (.parsed (.dateRange (.exact range)))).toOption
  let start ← (elaborateDateRangeBound yearMonthModel yearMonthTravel.id .start)
    |>.toOption
  let finish ← (elaborateDateRangeBound yearMonthModel yearMonthTravel.id .finish)
    |>.toOption
  let comparison ← (elaborateDateRangeBoundComparison yearMonthModel
    yearMonthTravel.id .finish .left .after februaryTwentyEighth).toOption
  let component ← (elaborateDateRangeBoundComponent yearMonthModel
    yearMonthTravel.id .finish .day).toOption
  let startValue ← (start.evaluate .validation input).toOption
  let finishValue ← (finish.evaluate .validation input).toOption
  let comparisonResult ← (comparison.evaluate input).toOption
  let componentResult ← (component.evaluate input).toOption
  pure (startValue, finishValue, comparisonResult.verdict,
    componentResult.component)

/- Year-month bounds retain leap-aware latest-day identity; the ordinary-year control rejects a fixed February-29 account. -/
example :
    yearMonthBoundConsumerSnapshot february2024 "2024-02/2024-02"
      (fullDate 2024 2 28 (by native_decide)) = some (
      .value february2024.start,
      .value february2024.finish,
      .fired .value,
      .value 29 .fixed) ∧
    yearMonthBoundConsumerSnapshot february2023 "2023-02/2023-02"
      (fullDate 2023 2 28 (by native_decide)) = some (
      .value february2023.start,
      .value february2023.finish,
      .notFired,
      .value 28 .fixed) := by
  native_decide

private def configuredMonthBoundConsumerSnapshot (baseYear : Int)
    (range : DateRangeValue) (stored : String)
    (februaryTwentyEighth : FullDate) : Option
      (DateRangeInputFormat × CellObservation DateValue ×
        CellObservation DateValue × Verdict × NumericOperand) := do
  let checkedModel := configuredMonthModel baseYear
  let prepared ← (prepareFlatStringContext { now := { epochMillis := 0 } }
    builtinStringPatternCompiler checkedModel).toOption
  let input ← (checkDocument prepared "en_US" {
    instantiatedRows := []
    cells := [{
      address := { field := monthTravel.id, path := [] }
      stored
      raw := .parsed (.dateRange (.exact range))
    }]
  }).toOption
  let start ← (elaborateDateRangeBound checkedModel monthTravel.id .start)
    |>.toOption
  let finish ← (elaborateDateRangeBound checkedModel monthTravel.id .finish)
    |>.toOption
  let comparison ← (elaborateDateRangeBoundComparison checkedModel
    monthTravel.id .finish .left .after februaryTwentyEighth).toOption
  let component ← (elaborateDateRangeBoundComponent checkedModel
    monthTravel.id .finish .day).toOption
  let startValue ← (start.evaluate .validation input).toOption
  let finishValue ← (finish.evaluate .validation input).toOption
  let comparisonResult ← (comparison.evaluate input).toOption
  let componentResult ← (component.evaluate input).toOption
  pure (start.format, startValue, finishValue, comparisonResult.verdict,
    componentResult.component)

/- Configured `MM` retains its model-owned year and leap-aware end; the ordinary-year control rejects fixed February completion. -/
example :
    configuredMonthBoundConsumerSnapshot 2024 february2024 "02/02"
      (fullDate 2024 2 28 (by native_decide)) = some (
      .yearlessMonth,
      .value february2024.start,
      .value february2024.finish,
      .fired .value,
      .value 29 .fixed) := by
  native_decide

example :
    configuredMonthBoundConsumerSnapshot 2023 february2023 "02/02"
      (fullDate 2023 2 28 (by native_decide)) = some (
      .yearlessMonth,
      .value february2023.start,
      .value february2023.finish,
      .notFired,
      .value 28 .fixed) := by
  native_decide

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

end A12Kernel.Conformance.DateRangeBound
