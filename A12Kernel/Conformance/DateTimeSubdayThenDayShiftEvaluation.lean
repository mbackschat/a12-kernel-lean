import A12Kernel.Elaboration.DateTimeSubdayThenDayShiftEvaluation

/-! # Elapsed-sub-day then calendar-day DateTime locks -/

namespace A12Kernel.Conformance.DateTimeSubdayThenDayShiftEvaluation

open A12Kernel

private def source : FlatFieldDecl := {
  id := 1
  groupPath := ["Order"]
  name := "ScheduledAt"
  policy := { kind := .temporal .dateTime TemporalComponents.now } }

private def innerAmount : FlatFieldDecl := {
  id := 2
  groupPath := ["Order"]
  name := "InnerAmount"
  policy := { kind := .number { scale := 2, signed := true } } }

private def outerAmount : FlatFieldDecl := {
  id := 3
  groupPath := ["Order"]
  name := "OuterAmount"
  policy := { kind := .number { scale := 2, signed := true } } }

private def innerAmountPath : SurfaceFieldPath := {
  base := .absolute
  groups := ["Order"]
  field := "InnerAmount" }

private def innerAmountOverZero : AuthoredNumericExpr SurfaceNumericAtom :=
  .binary .divide
    (.atom (.field innerAmountPath))
    (.literal { value := 0, authoredScale := 0 })

private def model : FlatModel := {
  fields := [source, innerAmount, outerAmount]
  timeZoneId := "Europe/Berlin" }

private def prepared? :=
  (prepareFlatStringContext { now := { epochMillis := 0 } }
    builtinStringPatternCompiler model).toOption

private def document?
    (cells : List ClassifiedCellInput) : Option (CheckedDocument model) := do
  let prepared ← prepared?
  checkDocument prepared "en_US" {
    instantiatedRows := []
    cells
  } |>.toOption

private def sourceCell (label : LocalDateTime)
    (instant : Instant) : ClassifiedCellInput := {
  address := { field := 1, path := [] }
  stored := "DateTime"
  raw := .parsed (.temporal (.dateTime instant
    label.date.civil.parts label.time .storedGregorian))
}

/- Elapsed arithmetic runs first; the calendar landing then consumes its exact instant
   and source offset. Ordinary carry, a gap, and an overlap all retain milliseconds. -/
example : (do
    let evaluate (sourceLabel : LocalDateTime) (millisecond : Int)
        (hours days : Rat) := do
      let resolved ←
        ModelZone.ConcreteProfile.europeBerlin.resolveLocal? sourceLabel
      let sourceInstant : Instant := {
        epochMillis := resolved.epochMillis + millisecond
      }
      let input ← document? [sourceCell sourceLabel sourceInstant]
      let checked ←
        (elaborateShiftedDateTimeSource model
          1 .hours (.literal hours)).toOption
      checked.evaluateThenDays (.literal days) .computation input |>.toOption
    let ordinary ← LocalDateTime.ofYmdHms? 2024 6 15 23 30 0
    let spring ← LocalDateTime.ofYmdHms? 2024 3 30 1 30 0
    let autumn ← LocalDateTime.ofYmdHms? 2024 10 26 1 30 0
    pure (
      ← evaluate ordinary 777 2 1,
      ← evaluate spring 333 1 1,
      ← evaluate autumn 444 1 1)) =
      some (
        ValueAsDateTimeResult.value
          ((LocalDateTime.ofYmdHms? 2024 6 17 1 30 0).get (by native_decide))
          { epochMillis := 1718580600777 } false,
        ValueAsDateTimeResult.value
          ((LocalDateTime.ofYmdHms? 2024 3 31 1 30 0).get (by native_decide))
          { epochMillis := 1711845000333 } false,
        ValueAsDateTimeResult.value
          ((LocalDateTime.ofYmdHms? 2024 10 27 2 30 0).get (by native_decide))
          { epochMillis := 1729989000444 } false) := by
  native_decide

/- Inner-before-outer order remains visible across the mechanism boundary. A formal
   inner result stops; arithmetic no-value reaches a formal outer amount; value-carrying
   omission accumulates; outer arithmetic no-value remains valueless. -/
example : (do
    let sourceLabel ← LocalDateTime.ofYmdHms? 2024 6 15 10 30 0
    let sourceInstant ←
      ModelZone.ConcreteProfile.europeBerlin.resolveLocal? sourceLabel
    let input (cells : List ClassifiedCellInput) :=
      document? (sourceCell sourceLabel sourceInstant :: cells)
    let innerField ←
      (elaborateValueAsDateTimeFieldShiftAmount model 2).toOption
    let outerField ←
      (elaborateValueAsDateTimeFieldShiftAmount model 3).toOption
    let checkedField ←
      (elaborateShiftedDateTimeSource model 1 .hours innerField).toOption
    let stoppedInput ← input [
      { address := { field := 2, path := [] }, stored := "bad-inner",
        raw := .rejected .malformed },
      { address := { field := 3, path := [] }, stored := "0.001",
        raw := .rejected .declaredConstraint }]
    let stopped ←
      checkedField.evaluateThenDays outerField .computation stoppedInput
        |>.toOption
    let innerDomain ←
      (elaborateValueAsDateTimeExpressionShiftAmount
        model ["Order"] innerAmountOverZero).toOption
    let checkedDomain ←
      (elaborateShiftedDateTimeSource model 1 .hours innerDomain).toOption
    let reachedInput ← input [
      { address := { field := 2, path := [] }, stored := "3",
        raw := .parsed (.num 3) },
      { address := { field := 3, path := [] }, stored := "0.001",
        raw := .rejected .declaredConstraint }]
    let reached ←
      checkedDomain.evaluateThenDays outerField .computation reachedInput
        |>.toOption
    let omittedInput ← input []
    let omitted ←
      checkedField.evaluateThenDays (.literal 1) .computation omittedInput
        |>.toOption
    let fixed ←
      (elaborateShiftedDateTimeSource model
        1 .seconds (.literal 0)).toOption
    let domainInput ← input [{
      address := { field := 2, path := [] }, stored := "3",
      raw := .parsed (.num 3) }]
    let outerDomain ←
      fixed.evaluateThenDays innerDomain .computation domainInput |>.toOption
    pure (stopped, reached, omitted, outerDomain)) =
      some (
        ValueAsDateTimeResult.unavailable .malformed,
        ValueAsDateTimeResult.unavailable .declaredConstraint,
        ValueAsDateTimeResult.value
          ((LocalDateTime.ofYmdHms? 2024 6 16 10 30 0).get (by native_decide))
          { epochMillis := 1718526600000 } true,
        ValueAsDateTimeResult.noValue false) := by
  native_decide

/- Each dynamic composition uses the supplied world's exact instant. Elapsed
   arithmetic still precedes the source-offset calendar landing at ordinary, gap, and
   overlap labels, with no loss of milliseconds. -/
example : (do
    let input ← document? []
    let evaluate (sourceLabel : LocalDateTime) (millisecond : Int)
        (hours days : Rat) := do
      let resolved ←
        ModelZone.ConcreteProfile.europeBerlin.resolveLocal? sourceLabel
      let world : World := {
        now := { epochMillis := resolved.epochMillis + millisecond }
      }
      let checked ←
        (elaborateShiftedNowDateTimeSource model
          .hours (.literal hours)).toOption
      checked.evaluateThenDays (.literal days)
        .computation world input |>.toOption
    let ordinary ← LocalDateTime.ofYmdHms? 2024 6 15 23 30 0
    let spring ← LocalDateTime.ofYmdHms? 2024 3 30 1 30 0
    let autumn ← LocalDateTime.ofYmdHms? 2024 10 26 1 30 0
    pure (
      ← evaluate ordinary 777 2 1,
      ← evaluate spring 333 1 1,
      ← evaluate autumn 444 1 1)) =
      some (
        ValueAsDateTimeResult.value
          ((LocalDateTime.ofYmdHms? 2024 6 17 1 30 0).get (by native_decide))
          { epochMillis := 1718580600777 } false,
        ValueAsDateTimeResult.value
          ((LocalDateTime.ofYmdHms? 2024 3 31 1 30 0).get (by native_decide))
          { epochMillis := 1711845000333 } false,
        ValueAsDateTimeResult.value
          ((LocalDateTime.ofYmdHms? 2024 10 27 2 30 0).get (by native_decide))
          { epochMillis := 1729989000444 } false) := by
  native_decide

/- The dynamic carrier has the same cross-mechanism cause and omission order without
   being merged with field-backed execution. -/
example : (do
    let nowLabel ← LocalDateTime.ofYmdHms? 2024 6 15 10 30 0
    let nowInstant ←
      ModelZone.ConcreteProfile.europeBerlin.resolveLocal? nowLabel
    let world : World := { now := nowInstant }
    let innerField ←
      (elaborateValueAsDateTimeFieldShiftAmount model 2).toOption
    let outerField ←
      (elaborateValueAsDateTimeFieldShiftAmount model 3).toOption
    let checkedField ←
      (elaborateShiftedNowDateTimeSource model .hours innerField).toOption
    let stoppedInput ← document? [
      { address := { field := 2, path := [] }, stored := "bad-inner",
        raw := .rejected .malformed },
      { address := { field := 3, path := [] }, stored := "0.001",
        raw := .rejected .declaredConstraint }]
    let stopped ←
      checkedField.evaluateThenDays outerField
        .computation world stoppedInput |>.toOption
    let innerDomain ←
      (elaborateValueAsDateTimeExpressionShiftAmount
        model ["Order"] innerAmountOverZero).toOption
    let checkedDomain ←
      (elaborateShiftedNowDateTimeSource model .hours innerDomain).toOption
    let reachedInput ← document? [
      { address := { field := 2, path := [] }, stored := "3",
        raw := .parsed (.num 3) },
      { address := { field := 3, path := [] }, stored := "0.001",
        raw := .rejected .declaredConstraint }]
    let reached ←
      checkedDomain.evaluateThenDays outerField
        .computation world reachedInput |>.toOption
    let omittedInput ← document? []
    let omitted ←
      checkedField.evaluateThenDays (.literal 1)
        .computation world omittedInput |>.toOption
    let fixed ←
      (elaborateShiftedNowDateTimeSource model
        .seconds (.literal 0)).toOption
    let domainInput ← document? [{
      address := { field := 2, path := [] }, stored := "3",
      raw := .parsed (.num 3) }]
    let outerDomain ←
      fixed.evaluateThenDays innerDomain
        .computation world domainInput |>.toOption
    pure (stopped, reached, omitted, outerDomain)) =
      some (
        ValueAsDateTimeResult.unavailable .malformed,
        ValueAsDateTimeResult.unavailable .declaredConstraint,
        ValueAsDateTimeResult.value
          ((LocalDateTime.ofYmdHms? 2024 6 16 10 30 0).get (by native_decide))
          { epochMillis := 1718526600000 } true,
        ValueAsDateTimeResult.noValue false) := by
  native_decide

end A12Kernel.Conformance.DateTimeSubdayThenDayShiftEvaluation
