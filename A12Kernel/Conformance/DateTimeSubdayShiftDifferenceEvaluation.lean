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

end A12Kernel.Conformance.DateTimeSubdayShiftDifferenceEvaluation
