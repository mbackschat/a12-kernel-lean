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

private def compositionPrepared :=
  (prepareFlatStringContext { now := { epochMillis := 0 } }
    builtinStringPatternCompiler compositionModel).toOption.get
      (by native_decide)

private def compositionInput?
    (cells : List ClassifiedCellInput) :
    Option (CheckedDocument compositionModel) :=
  checkDocument compositionPrepared "en_US" {
    instantiatedRows := []
    cells
  } |>.toOption

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

/- One checked dynamic day composition observes the world supplied to each call.
   The spring-gap result is a calendar-day count, not elapsed milliseconds divided by
   one day, and authored operand position controls its sign. -/
example : (do
    let otherLocal ← LocalDateTime.ofYmdHms? 2024 4 1 1 45 0
    let otherInstant ←
      ModelZone.ConcreteProfile.europeBerlin.resolveLocal? otherLocal
    let input ←
      compositionInput? [dateTimeCell other.id otherInstant otherLocal]
    let firstLocal ← LocalDateTime.ofYmdHms? 2024 3 29 2 30 0
    let secondLocal ← LocalDateTime.ofYmdHms? 2024 3 30 2 30 0
    let firstNow ←
      ModelZone.ConcreteProfile.europeBerlin.resolveLocal? firstLocal
    let secondNow ←
      ModelZone.ConcreteProfile.europeBerlin.resolveLocal? secondLocal
    let first ←
      (elaborateNowDateTimeDayShiftDifference compositionModel
        (.literal 1) other.id .first).toOption
    let second ←
      (elaborateNowDateTimeDayShiftDifference compositionModel
        (.literal 1) other.id .second).toOption
    let firstEarlier ←
      first.evaluate .validation { now := firstNow } input |>.toOption
    let firstLater ←
      first.evaluate .validation { now := secondNow } input |>.toOption
    let secondLater ←
      second.evaluate .validation { now := secondNow } input |>.toOption
    let landed ←
      first.shift.evaluate .validation { now := secondNow } input |>.toOption
    let elapsedUnderDay :=
      match landed with
      | .value _ instant _ =>
          otherInstant.epochMillis - instant.epochMillis < 86400000
      | _ => false
    pure (firstEarlier, firstLater, secondLater, elapsedUnderDay)) =
    some (
      .value 2 .fixed,
      .value 1 .fixed,
      .value (-1) .fixed,
      true) := by
  native_decide

/- The dynamic day shift retains the earlier repeated-midnight instant selected from
   its source offset before the direct sibling enters the calendar-day core. -/
example : (do
    let nowLocal ← LocalDateTime.ofYmdHms? 1916 9 30 0 0 0
    let now ← ModelZone.ConcreteProfile.europeBerlin.resolveLocal? nowLocal
    let otherLocal ← LocalDateTime.ofYmdHms? 1916 10 2 0 0 0
    let otherInstant ←
      ModelZone.ConcreteProfile.europeBerlin.resolveLocal? otherLocal
    let input ←
      compositionInput? [dateTimeCell other.id otherInstant otherLocal]
    let operation ←
      (elaborateNowDateTimeDayShiftDifference compositionModel
        (.literal 1) other.id .first).toOption
    let shifted ←
      operation.shift.evaluate .validation { now } input |>.toOption
    let result ←
      operation.evaluate .validation { now } input |>.toOption
    pure (shifted, result)) =
    some (
      .value
        ((LocalDateTime.ofYmdHms? 1916 10 1 0 0 0).get (by native_decide))
        { epochMillis := -1680487200000 } false,
      .value 1 .fixed) := by
  native_decide

/- Authored order decides whether a formal dynamic amount or direct DateTime cause
   wins. Missing amount retains a concrete zero shift with fillability; arithmetic
   no-value keeps the shared symmetric-zero result. -/
example : (do
    let nowLocal ← LocalDateTime.ofYmdHms? 2024 6 15 10 0 0
    let now ← ModelZone.ConcreteProfile.europeBerlin.resolveLocal? nowLocal
    let badInput ← compositionInput? [
      { address := { field := other.id, path := [] }
        stored := "bad-other"
        raw := .rejected .malformed },
      { address := { field := amount.id, path := [] }
        stored := "0.1"
        raw := .rejected .declaredConstraint }]
    let fieldAmount ←
      (elaborateValueAsDateTimeFieldShiftAmount
        compositionModel amount.id).toOption
    let first ←
      (elaborateNowDateTimeDayShiftDifference compositionModel
        fieldAmount other.id .first).toOption
    let second ←
      (elaborateNowDateTimeDayShiftDifference compositionModel
        fieldAmount other.id .second).toOption
    let badFirst ←
      first.evaluate .computation { now } badInput |>.toOption
    let badSecond ←
      second.evaluate .computation { now } badInput |>.toOption
    let otherLocal ← LocalDateTime.ofYmdHms? 2024 6 16 10 0 0
    let otherInstant ←
      ModelZone.ConcreteProfile.europeBerlin.resolveLocal? otherLocal
    let valueInput ←
      compositionInput? [dateTimeCell other.id otherInstant otherLocal]
    let omitted ←
      (elaborateNowDateTimeDayShiftDifference compositionModel
        fieldAmount other.id .first).toOption
    let omittedResult ←
      omitted.evaluate .computation { now } valueInput |>.toOption
    let domainAmount ←
      (elaborateValueAsDateTimeExpressionShiftAmount
        compositionModel ["Order"]
        (.binary .divide
          (.literal { value := 1, authoredScale := 0 })
          (.literal { value := 0, authoredScale := 0 }))).toOption
    let domain ←
      (elaborateNowDateTimeDayShiftDifference compositionModel
        domainAmount other.id .first).toOption
    let domainResult ←
      domain.evaluate .computation { now } valueInput |>.toOption
    pure (badFirst, badSecond, omittedResult, domainResult)) =
    some (
      .unknown .declaredConstraint,
      .unknown .malformed,
      .value 1 .both,
      .value 0 .both) := by
  native_decide

end A12Kernel.Conformance.DateTimeDayShiftEvaluation
