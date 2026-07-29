import A12Kernel.Elaboration.DateTimeDayShiftDifferenceEvaluation

/-! # Checked DateTime calendar-day shift locks -/

namespace A12Kernel.Conformance.DateTimeDayShiftEvaluation

open A12Kernel

private def source : FlatFieldDecl := {
  id := 1
  groupPath := ["Order"]
  name := "ScheduledAt"
  policy := {
    kind := .temporal .dateTime TemporalComponents.now
  }
}

private def model (zoneId : String) : FlatModel := {
  fields := [source]
  timeZoneId := zoneId
}

private def other : FlatFieldDecl := {
  id := 2
  groupPath := ["Order"]
  name := "FinishedAt"
  policy := {
    kind := .temporal .dateTime TemporalComponents.now
  }
}

private def amount : FlatFieldDecl := {
  id := 3
  groupPath := ["Order"]
  name := "Days"
  policy := {
    kind := .number { scale := 0, signed := true }
  }
}

private def compositionModel : FlatModel := {
  fields := [source, other, amount]
  timeZoneId := "Europe/Berlin"
}

private def document? (checkedModel : FlatModel)
    (instant : Instant) (localDateTime : LocalDateTime) :
    Option (CheckedDocument checkedModel) := do
  let prepared ←
    (prepareFlatStringContext { now := { epochMillis := 0 } }
      builtinStringPatternCompiler checkedModel).toOption
  checkDocument prepared "en_US" {
    instantiatedRows := []
    cells := [{
      address := { field := 1, path := [] }
      stored := "DateTime"
      raw := .parsed (.temporal (.dateTime instant
        localDateTime.date.civil.parts localDateTime.time .storedGregorian))
    }]
  } |>.toOption

private def dateTimeCell (field : FieldId)
    (instant : Instant) (localDateTime : LocalDateTime) :
    ClassifiedCellInput := {
  address := { field, path := [] }
  stored := "DateTime"
  raw := .parsed (.temporal (.dateTime instant
    localDateTime.date.civil.parts localDateTime.time .storedGregorian))
}

private def shift? (zoneId : String)
    (sourceLocal : LocalDateTime) (amount : Rat)
    (millisecond : Int := 0) := do
  let checkedModel := model zoneId
  let profile ← ModelZone.ConcreteProfile.ofId? zoneId
  let resolved ← profile.resolveLocal? sourceLocal
  let sourceInstant : Instant := {
    epochMillis := resolved.epochMillis + millisecond
  }
  let input ← document? checkedModel sourceInstant sourceLocal
  let checked ←
    (elaborateDateTimeDayShift
      checkedModel 1 (.literal amount)).toOption
  some (checked.evaluate .validation input)

private def berlinLongRangeGap? : Option Bool := do
  let sourceLocal ← LocalDateTime.ofYmdHms? 2023 8 31 2 30 0
  let forward ← shift? "Europe/Berlin" sourceLocal 213
  let reverseLocal ← LocalDateTime.ofYmdHms? 2024 11 30 2 30 0
  let reverse ← shift? "Europe/Berlin" reverseLocal (-244)
  let utcLocal ← LocalDateTime.ofYmdHms? 2024 6 15 10 30 45
  let utc ← shift? "UTC" utcLocal 1 777
  pure (match forward, reverse, utc with
    | .ok (.value
        { date := date, time := time }
        { epochMillis := 1711848600000 } false),
      .ok (.value
        { date := reverseDate, time := reverseTime }
        { epochMillis := 1711845000000 } false),
      .ok (.value utcResult
        { epochMillis := utcInstant } false) =>
        date.civil.parts == { year := 2024, month := 3, day := 31 } &&
          time.hour == 3 && time.minute == 30 && time.second == 0 &&
        reverseDate.civil.parts ==
          { year := 2024, month := 3, day := 31 } &&
          reverseTime.hour == 1 && reverseTime.minute == 30 &&
          reverseTime.second == 0 &&
        utcResult.date.civil.parts ==
          { year := 2024, month := 6, day := 16 } &&
          utcResult.time == utcLocal.time &&
          utcInstant == utcLocal.resolveUtc.epochMillis + 86400000 + 777
    | _, _, _ => false)

/- Calendar-day addition carries the distant source offset into the Berlin spring gap. Elapsed 24-hour shifting would land at a different local clock. -/
example : berlinLongRangeGap? = some true := by
  native_decide

private def nestedOverlap? : Option ValueAsDateTimeResult := do
  let overlapSource ← LocalDateTime.ofYmdHms? 1916 9 30 0 0 0
  let overlapInstant ←
    ModelZone.ConcreteProfile.europeBerlin.resolveLocal? overlapSource
  let checkedModel := model "Europe/Berlin"
  let overlapInput ←
    document? checkedModel overlapInstant overlapSource
  let overlapShift ←
    (elaborateDateTimeDayShift
      checkedModel 1 (.literal 1)).toOption
  overlapShift.evaluateThen (.literal 0) .validation overlapInput
    |>.toOption

/- A nested zero shift preserves the inner repeated-midnight CEST instant instead of
   resolving the carried wall label again to its CET sibling. -/
example :
    nestedOverlap? = some (
      .value
        ((LocalDateTime.ofYmdHms? 1916 10 1 0 0 0).get (by native_decide))
        { epochMillis := -1680487200000 } false) := by
  native_decide

private def differenceSnapshot? :
    Option (NumericOperand × NumericOperand × NumericOperand) := do
  let prepared ←
    (prepareFlatStringContext { now := { epochMillis := 0 } }
      builtinStringPatternCompiler compositionModel).toOption
  let springSource ← LocalDateTime.ofYmdHms? 2024 3 30 2 30 0
  let springInstant ←
    ModelZone.ConcreteProfile.europeBerlin.resolveLocal? springSource
  let springLater ← LocalDateTime.ofYmdHms? 2024 3 31 1 45 0
  let springLaterInstant ←
    ModelZone.ConcreteProfile.europeBerlin.resolveLocal? springLater
  let springInput ← checkDocument prepared "en_US" {
    instantiatedRows := []
    cells := [
      dateTimeCell 1 springInstant springSource,
      dateTimeCell 2 springLaterInstant springLater
    ]
  } |>.toOption
  let first ←
    (elaborateDateTimeDayShiftDifference compositionModel
      1 (.literal 0) 2 .first).toOption
  let second ←
    (elaborateDateTimeDayShiftDifference compositionModel
      1 (.literal 0) 2 .second).toOption
  let omitted ←
    (elaborateDateTimeDayShiftDifference compositionModel
      1 (.field {
        id := 3
        info := { scale := 0, signed := true }
      } (by native_decide)) 2 .first).toOption
  let firstResult ← first.evaluate .validation springInput |>.toOption
  let secondResult ← second.evaluate .validation springInput |>.toOption
  let omittedResult ← omitted.evaluate .validation springInput |>.toOption
  pure (firstResult, secondResult, omittedResult)

/- Mixed differences retain authored sign, and a value-carrying omitted shift amount
   makes the Number result fillable instead of erasing that provenance. -/
example :
    differenceSnapshot? = some (
      .value 1 .fixed,
      .value (-1) .fixed,
      .value 1 .both) := by
  native_decide

end A12Kernel.Conformance.DateTimeDayShiftEvaluation
