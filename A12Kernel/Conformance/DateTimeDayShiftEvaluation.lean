import A12Kernel.Elaboration.DateTimeDayShiftEvaluation

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

end A12Kernel.Conformance.DateTimeDayShiftEvaluation
