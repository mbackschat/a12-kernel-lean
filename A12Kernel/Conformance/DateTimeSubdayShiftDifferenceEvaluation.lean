import A12Kernel.Elaboration.DateTimeSubdayShiftDifferenceEvaluation

/-! # Checked DateTime sub-day shift/difference locks -/

namespace A12Kernel.Conformance.DateTimeSubdayShiftDifferenceEvaluation

open A12Kernel

private def dateTimeField (id : FieldId) (name : String) : FlatFieldDecl := {
  id
  groupPath := ["Order"]
  name
  policy := { kind := .temporal .dateTime TemporalComponents.now } }

private def amount : FlatFieldDecl := {
  id := 3
  groupPath := ["Order"]
  name := "Offset"
  policy := { kind := .number { scale := 0, signed := true } } }

private def model : FlatModel := {
  fields := [dateTimeField 1 "First", dateTimeField 2 "Second", amount]
  timeZoneId := "Europe/Berlin" }

private def prepared :=
  (prepareFlatStringContext { now := { epochMillis := 0 } }
    builtinStringPatternCompiler model).toOption.get (by native_decide)

private def dateTimeCell? (field : FieldId) (localDateTime : LocalDateTime)
    (millisecond : Int := 0) : Option ClassifiedCellInput := do
  let instant ←
    ModelZone.ConcreteProfile.europeBerlin.resolveLocal? localDateTime
  pure {
    address := { field, path := [] }
    stored := "date-time"
    raw := .parsed (.temporal (.dateTime
      { epochMillis := instant.epochMillis + millisecond }
      localDateTime.date.civil.parts localDateTime.time .storedGregorian))
  }

private def input? (cells : List ClassifiedCellInput) :
    Option (CheckedDocument model) :=
  checkDocument prepared "en_US" { instantiatedRows := [], cells } |>.toOption

private def operation? (differenceUnit : DateTimeSubdayUnit)
    (position : ShiftDifferencePosition)
    (shiftAmount : CheckedTemporalShiftAmount model := .literal 1) :=
  (elaborateDateTimeSubdayShiftDifference model
    1 .seconds shiftAmount 2 differenceUnit position).toOption

/- The retained millisecond identity reaches all three elapsed units, and authored
   operand position controls only the sign. -/
example : (do
    let first ← LocalDateTime.ofYmdHms? 2024 6 15 10 0 0
    let second ← LocalDateTime.ofYmdHms? 2024 6 15 12 30 2
    let firstCell ← dateTimeCell? 1 first 500
    let secondCell ← dateTimeCell? 2 second 999
    let input ← input? [firstCell, secondCell]
    let evaluate (unit : DateTimeSubdayUnit)
        (position : ShiftDifferencePosition) := do
      let operation ← operation? unit position
      operation.evaluate .validation input |>.toOption
    pure (
      [← evaluate .hours .first, ← evaluate .minutes .first,
        ← evaluate .seconds .first],
      [← evaluate .hours .second, ← evaluate .minutes .second,
        ← evaluate .seconds .second])) =
      some (
        [.value 2 .fixed, .value 150 .fixed, .value 9001 .fixed],
        [.value (-2) .fixed, .value (-150) .fixed,
          .value (-9001) .fixed]) := by
  native_decide

/- Exact shift chaining keeps the daylight-side repeated-hour instant instead of
   re-resolving its 02:30 wall label to the standard-side sibling. -/
example : (do
    let first ← LocalDateTime.ofYmdHms? 2024 10 27 1 30 0
    let repeated ← LocalDateTime.ofYmdHms? 2024 10 27 2 30 0
    let firstCell ← dateTimeCell? 1 first
    let repeatedCell ← dateTimeCell? 2 repeated
    let input ← input? [firstCell, repeatedCell]
    let operation ←
      (elaborateDateTimeSubdayShiftDifference model
        1 .hours (.literal 1) 2 .minutes .first).toOption
    operation.evaluate .validation input |>.toOption) =
      some (.value 60 .fixed) := by
  native_decide

/- Authored first-cause order is retained. Arithmetic no-value becomes the existing
   symmetric zero, while an empty Number amount keeps a concrete result fillable. -/
example : (do
    let badInput ← input? [
      { address := { field := 1, path := [] }
        stored := "bad-first"
        raw := .rejected .malformed },
      { address := { field := 2, path := [] }
        stored := "bad-second"
        raw := .rejected .declaredConstraint }]
    let firstOperation ← operation? .seconds .first
    let secondOperation ← operation? .seconds .second
    let badFirst ← firstOperation.evaluate .computation badInput |>.toOption
    let badSecond ← secondOperation.evaluate .computation badInput |>.toOption
    let first ← LocalDateTime.ofYmdHms? 2024 6 15 10 0 0
    let second ← LocalDateTime.ofYmdHms? 2024 6 15 11 0 0
    let firstCell ← dateTimeCell? 1 first
    let secondCell ← dateTimeCell? 2 second
    let valueInput ← input? [firstCell, secondCell]
    let domainAmount ←
      (elaborateValueAsDateTimeExpressionShiftAmount model ["Order"]
        (.binary .divide
          (.literal { value := 1, authoredScale := 0 })
          (.literal { value := 0, authoredScale := 0 }))).toOption
    let domainOperation ← operation? .hours .first domainAmount
    let domain ← domainOperation.evaluate .computation valueInput |>.toOption
    let omittedAmount ←
      (elaborateValueAsDateTimeFieldShiftAmount model amount.id).toOption
    let omittedOperation ← operation? .hours .first omittedAmount
    let omitted ← omittedOperation.evaluate .computation valueInput |>.toOption
    pure (badFirst, badSecond, domain, omitted)) =
      some (
        .unknown .malformed,
        .unknown .declaredConstraint,
        .value 0 .both,
        .value 1 .both) := by
  native_decide

/- One checked dynamic composition observes the world supplied to each call; all three
   elapsed units retain exact shifted milliseconds rather than elaboration-time state. -/
example : (do
    let otherLocal ← LocalDateTime.ofYmdHms? 2024 6 15 12 30 2
    let otherCell ← dateTimeCell? 2 otherLocal 999
    let input ← input? [otherCell]
    let firstLocal ← LocalDateTime.ofYmdHms? 2024 6 15 10 0 0
    let secondLocal ← LocalDateTime.ofYmdHms? 2024 6 15 10 0 1
    let firstBase ←
      ModelZone.ConcreteProfile.europeBerlin.resolveLocal? firstLocal
    let secondBase ←
      ModelZone.ConcreteProfile.europeBerlin.resolveLocal? secondLocal
    let first : World := {
      now := { epochMillis := firstBase.epochMillis + 500 } }
    let second : World := {
      now := { epochMillis := secondBase.epochMillis + 500 } }
    let evaluate (world : World) (unit : DateTimeSubdayUnit) := do
      let operation ←
        (elaborateShiftedNowDateTimeDifference model
          .seconds (.literal 1) 2 unit .first).toOption
      operation.evaluate .validation world input |>.toOption
    pure (
      [← evaluate first .hours, ← evaluate first .minutes,
        ← evaluate first .seconds],
      [← evaluate second .hours, ← evaluate second .minutes,
        ← evaluate second .seconds])) =
      some (
        [.value 2 .fixed, .value 150 .fixed, .value 9001 .fixed],
        [.value 2 .fixed, .value 150 .fixed, .value 9000 .fixed]) := by
  native_decide

/- Dynamic exact shifting retains the daylight-side repeated-hour instant before the
   direct fresh DateTime supplies the standard-side sibling. -/
example : (do
    let nowLocal ← LocalDateTime.ofYmdHms? 2024 10 27 1 30 0
    let now ← ModelZone.ConcreteProfile.europeBerlin.resolveLocal? nowLocal
    let repeated ← LocalDateTime.ofYmdHms? 2024 10 27 2 30 0
    let repeatedCell ← dateTimeCell? 2 repeated
    let input ← input? [repeatedCell]
    let operation ←
      (elaborateShiftedNowDateTimeDifference model
        .hours (.literal 1) 2 .minutes .first).toOption
    operation.evaluate .validation { now } input |>.toOption) =
      some (.value 60 .fixed) := by
  native_decide

/- Authored order decides whether a formal dynamic amount or the direct DateTime cause
   wins. Arithmetic no-value still uses the shared symmetric-zero result. -/
example : (do
    let nowLocal ← LocalDateTime.ofYmdHms? 2024 6 15 10 0 0
    let now ← ModelZone.ConcreteProfile.europeBerlin.resolveLocal? nowLocal
    let badInput ← input? [
      { address := { field := 2, path := [] }
        stored := "bad-other"
        raw := .rejected .malformed },
      { address := { field := amount.id, path := [] }
        stored := "0.1"
        raw := .rejected .declaredConstraint }]
    let fieldAmount ←
      (elaborateValueAsDateTimeFieldShiftAmount model amount.id).toOption
    let first ←
      (elaborateShiftedNowDateTimeDifference model
        .seconds fieldAmount 2 .seconds .first).toOption
    let second ←
      (elaborateShiftedNowDateTimeDifference model
        .seconds fieldAmount 2 .seconds .second).toOption
    let badFirst ← first.evaluate .computation { now } badInput |>.toOption
    let badSecond ← second.evaluate .computation { now } badInput |>.toOption
    let otherLocal ← LocalDateTime.ofYmdHms? 2024 6 15 11 0 0
    let otherCell ← dateTimeCell? 2 otherLocal
    let valueInput ← input? [otherCell]
    let domainAmount ←
      (elaborateValueAsDateTimeExpressionShiftAmount model ["Order"]
        (.binary .divide
          (.literal { value := 1, authoredScale := 0 })
          (.literal { value := 0, authoredScale := 0 }))).toOption
    let domain ←
      (elaborateShiftedNowDateTimeDifference model
        .seconds domainAmount 2 .hours .first).toOption
    let domainResult ←
      domain.evaluate .computation { now } valueInput |>.toOption
    let omitted ←
      (elaborateShiftedNowDateTimeDifference model
        .seconds fieldAmount 2 .hours .first).toOption
    let omittedResult ←
      omitted.evaluate .computation { now } valueInput |>.toOption
    pure (badFirst, badSecond, domainResult, omittedResult)) =
      some (
        .unknown .declaredConstraint,
        .unknown .malformed,
        .value 0 .both,
        .value 1 .both) := by
  native_decide

end A12Kernel.Conformance.DateTimeSubdayShiftDifferenceEvaluation
