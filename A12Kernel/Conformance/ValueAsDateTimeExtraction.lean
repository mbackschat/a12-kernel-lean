import A12Kernel.Elaboration.ValueAsDateTimeExtraction

/-! # Partial-Date and `TimeFromDateTime` locks -/

namespace A12Kernel.Conformance.ValueAsDateTimeExtraction

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

private def modelWith
    (source : FlatFieldDecl := dateTimeSource)
    (timeZoneId : String := "Europe/Berlin") : FlatModel := {
  fields := [partialDate, source]
  timeZoneId }

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

/- Static admission requires a complete DateTime source, not merely a temporal value with a Time half. -/
example :
    let incomplete := { TemporalComponents.now with second := false }
    extractionError? (elaborateValueAsDateTimeExtraction
        (modelWith (dateTimeSource .time)) 0 .firstDay 1) =
        some (.sourceKind 1 .time) ∧
      extractionError? (elaborateValueAsDateTimeShiftExtraction
        (modelWith (dateTimeSource .time)) 0 .firstDay 1 .hours 1) =
        some (.sourceKind 1 .time) ∧
      extractionError? (elaborateValueAsDateTimeExtraction
        (modelWith (dateTimeSource .dateTime incomplete))
        0 .firstDay 1) =
        some (.sourceComponents 1 incomplete) := by
  native_decide

/- Time extraction uses the retained wall-clock half; exact instant identity and the date half are irrelevant after static DateTime admission. -/
example :
    let clock := (TimeOfDay.ofHms? 2 30 0).get (by native_decide)
    let date : DateParts := { year := 2024, month := 10, day := 27 }
    ValueAsDateTimeTimeOperand.ofDateTimeValueObservation
        (.value (.temporal (.dateTime
          { epochMillis := 1729989000000 } date clock .storedGregorian))) =
        some (.value clock) ∧
      ValueAsDateTimeTimeOperand.ofDateTimeValueObservation
        (.value (.temporal (.dateTime
          { epochMillis := 1729992600000 } date clock .storedGregorian))) =
        some (.value clock) := by
  native_decide

/- One checked DateTime field supplies the extracted Time and reaches the existing Berlin partial-Date constructor. -/
example :
    let model := modelWith
    let sourceDate : DateParts := { year := 2024, month := 6, day := 15 }
    let clock := (TimeOfDay.ofHms? 10 30 45).get (by native_decide)
    let expectedLocal := (LocalDateTime.ofYmdHms?
      2024 2 29 10 30 45).get (by native_decide)
    let expectedInstant :=
      (ModelZone.ConcreteProfile.europeBerlin.resolveLocal?
        expectedLocal).get (by native_decide)
    let result := do
      let checked ← (elaborateValueAsDateTimeExtraction
        model 0 .lastDay 1).toOption
      let input ← document? model [{
        address := { field := 1, path := [] }
        stored := "2024-06-15T10:30:45"
        raw := dateTimeRaw { epochMillis := 1718440245000 }
          sourceDate clock
      }]
      pure (checked.evaluateRaw .validation input
        (.parsed "00.02.2024") |>.toOption)
    result = some (some (.value expectedLocal expectedInstant)) := by
  native_decide

/- An empty DateTime input remains not-given at the shared Time seam. -/
example :
    let model := modelWith
    let result := do
      let checked ← (elaborateValueAsDateTimeExtraction
        model 0 .firstDay 1).toOption
      let input ← document? model []
      pure (checked.evaluateRaw .validation input
        (.parsed "15.06.2024") |>.toOption)
    result = some (some (.noValue true)) := by
  native_decide

/- Generated Date-before-Time evaluation preserves the first formal cause, while cause-free unknown-year non-relevance still reaches the DateTime read. -/
example :
    let model := modelWith
    let result (dateRaw : RawCell String) := do
      let checked ← (elaborateValueAsDateTimeExtraction
        model 0 .firstDay 1).toOption
      let input ← document? model [{
        address := { field := 1, path := [] }
        stored := "bad"
        raw := .rejected .malformed
      }]
      pure (checked.evaluateRaw .computation input dateRaw |>.toOption)
    result (.rejected .declaredConstraint) =
        some (some (.unavailable .declaredConstraint)) ∧
      result (.parsed "00.00.0000") =
        some (some (.unavailable .malformed)) := by
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
    result = some (some (.value expectedLocal expectedInstant)) := by
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
          (ValueAsDateShiftUnit.amountToInt32 4294967297) =
        { epochMillis := 1718440246000 } := by
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
    result = some (some (.value expectedLocal expectedInstant)) := by
  native_decide

end A12Kernel.Conformance.ValueAsDateTimeExtraction
