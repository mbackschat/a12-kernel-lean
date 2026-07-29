import A12Kernel.Elaboration.ValueAsDateTimeExtraction

/-! # Exact sub-day DateTime shift locks -/

namespace A12Kernel.Conformance.DateTimeSubdayShift

open A12Kernel

private def partialDate : FlatFieldDecl := {
  id := 0
  groupPath := ["Order"]
  name := "ApproxDate"
  policy := {
    kind := .temporal .date TemporalComponents.fullDate }
  temporalTargetPolicy := some {
    format := "dd.MM.yyyy"
    partialMode := .yearOptional
    youngerThan1900Check := false } }

private def dateTimeSource
    (kind : TemporalKind := .dateTime)
    (components : TemporalComponents := TemporalComponents.now) :
    FlatFieldDecl := {
  id := 1
  groupPath := ["Order"]
  name := "ScheduledAt"
  policy := { kind := .temporal kind components } }

private def shiftAmount : FlatFieldDecl := {
  id := 2
  groupPath := ["Order"]
  name := "ShiftAmount"
  policy := { kind := .number { scale := 2, signed := true } } }

private def shiftAmountPath : SurfaceFieldPath := {
  base := .absolute
  groups := ["Order"]
  field := "ShiftAmount" }

private def shiftedByFieldPlusOne : AuthoredNumericExpr SurfaceNumericAtom :=
  .binary .add
    (.atom (.field shiftAmountPath))
    (.literal { value := 1, authoredScale := 0 })

private def shiftedByFieldOverZero : AuthoredNumericExpr SurfaceNumericAtom :=
  .binary .divide
    (.atom (.field shiftAmountPath))
    (.literal { value := 0, authoredScale := 0 })

private def modelWith
    (source : FlatFieldDecl := dateTimeSource)
    (timeZoneId : String := "Europe/Berlin") : FlatModel := {
  fields := [partialDate, source]
  timeZoneId }

private def modelWithShiftAmount : FlatModel := {
  fields := [partialDate, dateTimeSource, shiftAmount]
  timeZoneId := "Europe/Berlin" }

private def prepared? (model : FlatModel) :=
  (prepareFlatStringContext { now := { epochMillis := 0 } }
    builtinStringPatternCompiler model).toOption

private def document? (model : FlatModel)
    (cells : List ClassifiedCellInput) : Option (CheckedDocument model) := do
  let prepared ← prepared? model
  checkDocument prepared "en_US" {
    instantiatedRows := []
    cells
  } |>.toOption

private def dateTimeRaw (instant : Instant)
    (date : DateParts) (clock : TimeOfDay) : RawCell :=
  .parsed (.temporal (.dateTime instant date clock .storedGregorian))

private def extractionError?
    (result : Except ValueAsDateTimeExtractionElabError value) :
    Option ValueAsDateTimeExtractionElabError :=
  match result with
  | .ok _ => none
  | .error error => some error

/- Shift admission requires a complete DateTime source, not merely a temporal value with a Time half. -/
example :
    let incomplete := { TemporalComponents.now with second := false }
    extractionError? (elaborateValueAsDateTimeShiftExtraction
        (modelWith (dateTimeSource .time)) 0 .firstDay 1 .hours 1) =
        some (.sourceKind 1 .time) ∧
      extractionError? (elaborateValueAsDateTimeShiftExtraction
        (modelWith (dateTimeSource .dateTime incomplete))
        0 .firstDay 1 .hours 1) =
        some (.sourceComponents 1 incomplete) := by
  native_decide

/- A sub-day shift acts on the exact DateTime instant before `TimeFromDateTime` projects the model-zone clock. Spring-forward therefore skips the nonexistent Berlin hour rather than adding to the wall label. -/
example :
    let model := modelWith
    let sourceLocal := (LocalDateTime.ofYmdHms?
      2024 3 31 1 30 0).get (by native_decide)
    let sourceInstant :=
      (ModelZone.ConcreteProfile.europeBerlin.resolveLocal?
        sourceLocal).get (by native_decide)
    let expectedLocal := (LocalDateTime.ofYmdHms?
      2024 2 29 3 30 0).get (by native_decide)
    let expectedInstant :=
      (ModelZone.ConcreteProfile.europeBerlin.resolveLocal?
        expectedLocal).get (by native_decide)
    let result := do
      let checked ← (elaborateValueAsDateTimeShiftExtraction
        model 0 .lastDay 1 .hours 1).toOption
      let input ← document? model [{
        address := { field := 1, path := [] }
        stored := "2024-03-31T01:30:00"
        raw := dateTimeRaw sourceInstant sourceLocal.date.civil.parts sourceLocal.time
      }]
      pure (checked.evaluateRaw .validation input
        (.parsed "00.02.2024") |>.toOption)
    result = some (some (.value expectedLocal expectedInstant false)) := by
  native_decide

/- A dynamic `Now` source is sampled from the execution world, shifted as an exact instant, and only then projected through the same Berlin Time boundary. -/
example :
    let model := modelWith
    let nowLocal := (LocalDateTime.ofYmdHms?
      2024 3 31 1 30 0).get (by native_decide)
    let now :=
      (ModelZone.ConcreteProfile.europeBerlin.resolveLocal?
        nowLocal).get (by native_decide)
    let expectedLocal := (LocalDateTime.ofYmdHms?
      2024 2 29 3 30 0).get (by native_decide)
    let expectedInstant :=
      (ModelZone.ConcreteProfile.europeBerlin.resolveLocal?
        expectedLocal).get (by native_decide)
    let result := do
      let checked ← (elaborateValueAsDateTimeNowShiftExtraction
        model 0 .lastDay .hours 1).toOption
      let input ← document? model []
      pure (checked.evaluateRaw .validation { now } input
        (.parsed "00.02.2024") |>.toOption)
    result = some (some (.value expectedLocal expectedInstant false)) := by
  native_decide

/- Exact millisecond identity survives `Now` and the shift but is intentionally unobservable after `TimeFromDateTime` projects a whole-second clock. Crossing the rendered-second boundary remains observable. -/
example :
    let model := modelWith
    let base := (LocalDateTime.ofYmdHms?
      2025 6 23 12 0 0).get (by native_decide)
    let epochMillis := base.resolveUtc.epochMillis
    let evaluate (millisecond : Int) := do
      let checked ← (elaborateValueAsDateTimeNowShiftExtraction
        model 0 .firstDay .seconds 1).toOption
      let input ← document? model []
      pure (checked.evaluateRaw .validation
        { now := { epochMillis := epochMillis + millisecond } }
        input
        (.parsed "15.06.2024") |>.toOption)
    evaluate 1 = evaluate 999 ∧ evaluate 999 ≠ evaluate 1000 := by
  native_decide

/- A dynamic `Now` source shares the checked Number-field amount semantics: fractional values narrow toward zero, while an empty field retains the concrete zero-shift value with omission provenance. -/
example :
    let model := modelWithShiftAmount
    let nowLocal := (LocalDateTime.ofYmdHms?
      2024 6 15 10 30 0).get (by native_decide)
    let now :=
      (ModelZone.ConcreteProfile.europeBerlin.resolveLocal?
        nowLocal).get (by native_decide)
    let shiftedLocal := (LocalDateTime.ofYmdHms?
      2024 6 15 10 31 0).get (by native_decide)
    let shiftedInstant :=
      (ModelZone.ConcreteProfile.europeBerlin.resolveLocal?
        shiftedLocal).get (by native_decide)
    let evaluate (amount : Option Rat) := do
      let checked ←
        (elaborateValueAsDateTimeNowFieldShiftExtraction
          model 0 .firstDay .minutes 2).toOption
      let amountCell := amount.toList.map fun value => {
        address := { field := 2, path := [] }
        stored := "1.5"
        raw := .parsed (.num value)
      }
      let input ← document? model amountCell
      pure (checked.evaluateRaw .validation { now } input
        (.parsed "15.06.2024") |>.toOption)
    evaluate (some (3 / 2)) =
        some (some (.value shiftedLocal shiftedInstant false)) ∧
      evaluate none =
        some (some (.value nowLocal now true)) := by
  native_decide

/- A formal field amount is reached after dynamic `Now` and remains formally unavailable. -/
example :
    let model := modelWithShiftAmount
    let nowLocal := (LocalDateTime.ofYmdHms?
      2024 6 15 10 30 0).get (by native_decide)
    let now :=
      (ModelZone.ConcreteProfile.europeBerlin.resolveLocal?
        nowLocal).get (by native_decide)
    let result := do
      let checked ←
        (elaborateValueAsDateTimeNowFieldShiftExtraction
          model 0 .firstDay .seconds 2).toOption
      let input ← document? model [{
        address := { field := 2, path := [] }
        stored := "0.001"
        raw := .rejected .declaredConstraint
      }]
      pure (checked.evaluateRaw .computation { now } input
        (.parsed "15.06.2024") |>.toOption)
    result = some (some (.unavailable .declaredConstraint)) := by
  native_decide

/- Shifting does not manufacture an instant for an empty or formally unavailable DateTime source. -/
example :
    let model := modelWith
    let evaluate (cells : List ClassifiedCellInput) := do
      let checked ← (elaborateValueAsDateTimeShiftExtraction
        model 0 .firstDay 1 .minutes 90).toOption
      let input ← document? model cells
      pure (checked.evaluateRaw .computation input
        (.parsed "15.06.2024") |>.toOption)
    evaluate [] = some (some (.noValue true)) ∧
      evaluate [{
        address := { field := 1, path := [] }
        stored := "bad"
        raw := .rejected .malformed
      }] = some (some (.unavailable .malformed)) := by
  native_decide

/- Unit selection and Java signed-32-bit narrowing happen before exact-instant arithmetic. The source Date and any crossed day are discarded only by the later Time projection. -/
example :
    let source : Instant := { epochMillis := 1718440245000 }
    source.shift .hours 1 = { epochMillis := 1718443845000 } ∧
      source.shift .minutes 1 = { epochMillis := 1718440305000 } ∧
      source.shift .seconds
          (temporalShiftAmountToInt32 4294967297) =
        { epochMillis := 1718440246000 } ∧
      source.shift .hours
          (temporalShiftAmountToInt32 2147483648) =
        { epochMillis := -7729222692555000 } := by
  native_decide

/- Negative rollover changes the shifted DateTime day, but the enclosing constructor keeps its independently evaluated partial-Date day and consumes only the shifted clock. -/
example :
    let model := modelWith
    let sourceLocal := (LocalDateTime.ofYmdHms?
      2024 6 15 0 30 0).get (by native_decide)
    let sourceInstant :=
      (ModelZone.ConcreteProfile.europeBerlin.resolveLocal?
        sourceLocal).get (by native_decide)
    let expectedLocal := (LocalDateTime.ofYmdHms?
      2024 2 29 23 30 0).get (by native_decide)
    let expectedInstant :=
      (ModelZone.ConcreteProfile.europeBerlin.resolveLocal?
        expectedLocal).get (by native_decide)
    let result := do
      let checked ← (elaborateValueAsDateTimeShiftExtraction
        model 0 .lastDay 1 .hours (-1)).toOption
      let input ← document? model [{
        address := { field := 1, path := [] }
        stored := "2024-06-15T00:30:00"
        raw := dateTimeRaw sourceInstant sourceLocal.date.civil.parts sourceLocal.time
      }]
      pure (checked.evaluateRaw .validation input
        (.parsed "00.02.2024") |>.toOption)
    result = some (some (.value expectedLocal expectedInstant false)) := by
  native_decide

/- A checked Number-field amount preserves both the helper's truncate-toward-zero conversion and the omission carried by an empty field. Empty is a zero shift with a value, not clean no-value. -/
example :
    let model := modelWithShiftAmount
    let sourceLocal := (LocalDateTime.ofYmdHms?
      2024 6 15 10 30 0).get (by native_decide)
    let sourceInstant :=
      (ModelZone.ConcreteProfile.europeBerlin.resolveLocal?
        sourceLocal).get (by native_decide)
    let shiftedLocal := (LocalDateTime.ofYmdHms?
      2024 6 15 10 31 0).get (by native_decide)
    let shiftedInstant :=
      (ModelZone.ConcreteProfile.europeBerlin.resolveLocal?
        shiftedLocal).get (by native_decide)
    let evaluate (amount : Option Rat) := do
      let checked ←
        (elaborateValueAsDateTimeFieldShiftExtraction
          model 0 .firstDay 1 .minutes 2).toOption
      let amountCell := amount.toList.map fun value => {
        address := { field := 2, path := [] }
        stored := "1.5"
        raw := .parsed (.num value)
      }
      let input ← document? model ({
        address := { field := 1, path := [] }
        stored := "2024-06-15T10:30:00"
        raw := dateTimeRaw sourceInstant sourceLocal.date.civil.parts sourceLocal.time
      } :: amountCell)
      pure (checked.evaluateRaw .validation input
        (.parsed "15.06.2024") |>.toOption)
    evaluate (some (3 / 2)) =
        some (some (.value shiftedLocal shiftedInstant false)) ∧
      evaluate none =
        some (some (.value sourceLocal sourceInstant true)) := by
  native_decide

/- Static amount admission rejects a resolved non-Number declaration before evaluation. -/
example :
    extractionError?
        (elaborateValueAsDateTimeFieldShiftExtraction
          modelWithShiftAmount 0 .firstDay 1 .minutes 1) =
        some (.amountNotNumber 1) ∧
      extractionError?
        (elaborateValueAsDateTimeNowFieldShiftExtraction
          modelWithShiftAmount 0 .firstDay .minutes 1) =
        some (.amountNotNumber 1) := by
  native_decide

/- Generated source-before-amount evaluation stops on a formal DateTime source, but an empty source still reaches and exposes a formal amount. -/
example :
    let model := modelWithShiftAmount
    let evaluate (cells : List ClassifiedCellInput) := do
      let checked ←
        (elaborateValueAsDateTimeFieldShiftExtraction
          model 0 .firstDay 1 .seconds 2).toOption
      let input ← document? model cells
      pure (checked.evaluateRaw .computation input
        (.parsed "15.06.2024") |>.toOption)
    evaluate [{
        address := { field := 1, path := [] }
        stored := "bad-date-time"
        raw := .rejected .malformed
      }, {
        address := { field := 2, path := [] }
        stored := "0.001"
        raw := .rejected .declaredConstraint
      }] = some (some (.unavailable .malformed)) ∧
      evaluate [{
        address := { field := 2, path := [] }
        stored := "0.001"
        raw := .rejected .declaredConstraint
      }] = some (some (.unavailable .declaredConstraint)) := by
  native_decide

/- A checked numeric expression reuses the numeric evaluator for its connective, fillability, formal cause, and domain-invalid no-value. Empty Number plus one remains a concrete omission-typed shift; division by zero does not become a zero shift. -/
example :
    let model := modelWithShiftAmount
    let sourceLocal := (LocalDateTime.ofYmdHms?
      2024 6 15 10 30 0).get (by native_decide)
    let sourceInstant :=
      (ModelZone.ConcreteProfile.europeBerlin.resolveLocal?
        sourceLocal).get (by native_decide)
    let shiftedOne := (LocalDateTime.ofYmdHms?
      2024 6 15 10 31 0).get (by native_decide)
    let shiftedOneInstant :=
      (ModelZone.ConcreteProfile.europeBerlin.resolveLocal?
        shiftedOne).get (by native_decide)
    let shiftedTwo := (LocalDateTime.ofYmdHms?
      2024 6 15 10 32 0).get (by native_decide)
    let shiftedTwoInstant :=
      (ModelZone.ConcreteProfile.europeBerlin.resolveLocal?
        shiftedTwo).get (by native_decide)
    let evaluate
        (expression : AuthoredNumericExpr SurfaceNumericAtom)
        (amount : Option (RawCell Value)) := do
      let checked ←
        (elaborateValueAsDateTimeExpressionShiftExtraction
          model ["Order"] 0 .firstDay 1 .minutes expression).toOption
      let amountCell := amount.toList.map fun raw => {
        address := { field := 2, path := [] }
        stored := match raw with
          | .parsed (.num value) =>
              if value = 3 / 2 then "1.5" else toString value
          | .rejected .declaredConstraint => "0.001"
          | .presentEmpty => ""
          | _ => "bad"
        raw
      }
      let input ← document? model ({
        address := { field := 1, path := [] }
        stored := "2024-06-15T10:30:00"
        raw := dateTimeRaw sourceInstant sourceLocal.date.civil.parts sourceLocal.time
      } :: amountCell)
      pure (checked.evaluateRaw .computation input
        (.parsed "15.06.2024") |>.toOption)
    evaluate shiftedByFieldPlusOne (some (.parsed (.num (3 / 2)))) =
        some (some (.value shiftedTwo shiftedTwoInstant false)) ∧
      evaluate shiftedByFieldPlusOne none =
        some (some (.value shiftedOne shiftedOneInstant true)) ∧
      evaluate shiftedByFieldPlusOne
          (some (.rejected .declaredConstraint)) =
        some (some (.unavailable .declaredConstraint)) ∧
    evaluate shiftedByFieldOverZero (some (.parsed (.num 3))) =
        some (some (.noValue false)) := by
  native_decide

/- The `Now` source accepts the same checked expression, while a statically valid non-field numeric atom stays outside this bounded shift capsule. -/
example :
    (elaborateValueAsDateTimeNowExpressionShiftExtraction
      modelWithShiftAmount ["Order"] 0 .firstDay .minutes
        shiftedByFieldPlusOne).isOk = true ∧
      extractionError?
        (elaborateValueAsDateTimeExpressionShiftExtraction
          { modelWithShiftAmount with baseYear := some 2020 }
          ["Order"] 0 .firstDay 1 .minutes (.atom .baseYear)) =
        some .amountExpressionNotDirectNumber := by
  native_decide

/- Whole sub-day evaluation retains the earlier repeated-midnight instant; the existing
   Time extractor is only its wall-clock projection, and fresh resolution selects the
   distinct later sibling. -/
example : (do
    let sourceLocal ← LocalDateTime.ofYmdHms? 1916 9 30 23 30 0
    let sourceInstant ←
      ModelZone.ConcreteProfile.europeBerlin.resolveLocal? sourceLocal
    let input ← document? modelWithShiftAmount [{
      address := { field := 1, path := [] }
      stored := "30.09.1916T23:30:00"
      raw := dateTimeRaw sourceInstant
        sourceLocal.date.civil.parts sourceLocal.time
    }]
    let checked ←
      (elaborateShiftedDateTimeSource
        modelWithShiftAmount 1 .hours (.literal 1)).toOption
    let whole ← checked.evaluate .computation input |>.toOption
    let time ← checked.readTime .computation input |>.toOption
    match whole with
    | .value label instant false =>
        let fresh ← checked.profile.resolveLocal? label
        pure (time = .value label.time false, instant ≠ fresh)
    | _ => none) = some (true, true) := by
  native_decide

/- A second checked sub-day shift consumes the inner exact instant directly. Cross-unit
   pairs preserve calendar carry, wall label, and the millisecond-relative delta. -/
example : (do
    let sourceLocal ← LocalDateTime.ofYmdHms? 2024 6 15 23 59 30
    let resolved ←
      ModelZone.ConcreteProfile.europeBerlin.resolveLocal? sourceLocal
    let sourceInstant : Instant := {
      epochMillis := resolved.epochMillis + 777
    }
    let input ← document? modelWithShiftAmount [{
      address := { field := 1, path := [] }
      stored := "15.06.2024T23:59:30"
      raw := dateTimeRaw sourceInstant
        sourceLocal.date.civil.parts sourceLocal.time
    }]
    let evaluate (firstUnit : DateTimeSubdayUnit) (firstAmount : Rat)
        (secondUnit : DateTimeSubdayUnit) (secondAmount : Rat)
        (hour minute second : Nat) (delta : Int) := do
      let checked ←
        (elaborateShiftedDateTimeSource modelWithShiftAmount
          1 firstUnit (.literal firstAmount)).toOption
      let result ←
        checked.evaluateThen secondUnit (.literal secondAmount)
          .computation input |>.toOption
      match result with
      | .value label instant false =>
          pure (label.date.civil.parts ==
              { year := 2024, month := 6, day := 16 } &&
            label.time.hour == hour && label.time.minute == minute &&
            label.time.second == second &&
            instant.epochMillis - sourceInstant.epochMillis == delta)
      | _ => none
    pure [
      ← evaluate .hours 1 .minutes 2 1 1 30 3720000,
      ← evaluate .minutes 2 .seconds 45 0 2 15 165000,
      ← evaluate .seconds 45 .hours 2 2 0 15 7245000
    ]) = some [true, true, true] := by
  native_decide

/- Nested evaluation preserves the inner repeated-hour instant. A formal inner source
   stops the outer amount; inner no-value reaches it; arithmetic no-value and inherited
   omission remain distinct. -/
example : (do
    let overlapLocal ← LocalDateTime.ofYmdHms? 2024 10 27 1 30 0
    let overlapInstant ←
      ModelZone.ConcreteProfile.europeBerlin.resolveLocal? overlapLocal
    let overlapInput ← document? modelWithShiftAmount [{
      address := { field := 1, path := [] }
      stored := "27.10.2024T01:30:00"
      raw := dateTimeRaw overlapInstant
        overlapLocal.date.civil.parts overlapLocal.time
    }]
    let overlap ←
      (elaborateShiftedDateTimeSource modelWithShiftAmount
        1 .hours (.literal 1)).toOption
    let nestedOverlap ←
      overlap.evaluateThen .seconds (.literal 0)
        .computation overlapInput |>.toOption
    let badSourceInput ← document? modelWithShiftAmount [
      { address := { field := 1, path := [] }
        stored := "bad-source"
        raw := .rejected .malformed },
      { address := { field := 2, path := [] }
        stored := "0.001"
        raw := .rejected .declaredConstraint }]
    let fixed ←
      (elaborateShiftedDateTimeSource modelWithShiftAmount
        1 .seconds (.literal 0)).toOption
    let outerField ←
      (elaborateValueAsDateTimeFieldShiftAmount
        modelWithShiftAmount 2).toOption
    let stopped ←
      fixed.evaluateThen .seconds outerField
        .computation badSourceInput |>.toOption
    let emptyInput ← document? modelWithShiftAmount [{
      address := { field := 2, path := [] }
      stored := "0.001"
      raw := .rejected .declaredConstraint }]
    let reached ←
      fixed.evaluateThen .seconds outerField .computation emptyInput |>.toOption
    let omittedInner ←
      (elaborateShiftedDateTimeSource modelWithShiftAmount
        1 .seconds outerField).toOption
    let omitted ←
      omittedInner.evaluateThen .seconds (.literal 1)
        .computation overlapInput |>.toOption
    let domainAmount ←
      (elaborateValueAsDateTimeExpressionShiftAmount
        modelWithShiftAmount ["Order"] shiftedByFieldOverZero).toOption
    let domainInput ← document? modelWithShiftAmount [
      { address := { field := 1, path := [] }
        stored := "27.10.2024T01:30:00"
        raw := dateTimeRaw overlapInstant
          overlapLocal.date.civil.parts overlapLocal.time },
      { address := { field := 2, path := [] }
        stored := "3"
        raw := .parsed (.num 3) }]
    let domain ←
      fixed.evaluateThen .seconds domainAmount .computation domainInput |>.toOption
    pure (nestedOverlap, stopped, reached, omitted, domain)) =
      some (
        .value
          ((LocalDateTime.ofYmdHms? 2024 10 27 2 30 0).get (by native_decide))
          { epochMillis := 1729989000000 } false,
        .unavailable .malformed,
        .unavailable .declaredConstraint,
        .value
          ((LocalDateTime.ofYmdHms? 2024 10 27 1 30 1).get (by native_decide))
          { epochMillis := 1729985401000 } true,
        .noValue false) := by
  native_decide

end A12Kernel.Conformance.DateTimeSubdayShift
