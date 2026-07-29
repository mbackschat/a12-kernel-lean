import A12Kernel.Elaboration.DateTimeDayThenSubdayShiftEvaluation

/-! # Calendar-day then elapsed-sub-day DateTime locks -/

namespace A12Kernel.Conformance.DateTimeDayThenSubdayShiftEvaluation

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

/- Calendar mutation runs first and elapsed arithmetic consumes its exact landing.
   Spring therefore reaches 03:30; autumn reaches the later instant at the same 02:30
   wall label. Milliseconds survive both operations. -/
example : (do
    let evaluate (sourceLabel : LocalDateTime) (millisecond : Int)
        (days hours : Rat) := do
      let resolved ←
        ModelZone.ConcreteProfile.europeBerlin.resolveLocal? sourceLabel
      let sourceInstant : Instant := {
        epochMillis := resolved.epochMillis + millisecond
      }
      let input ← document? [sourceCell sourceLabel sourceInstant]
      let checked ←
        (elaborateDateTimeDayShift model 1 (.literal days)).toOption
      checked.evaluateThenSubday .hours (.literal hours)
        .computation input |>.toOption
    let ordinary ← LocalDateTime.ofYmdHms? 2024 6 15 23 30 0
    let spring ← LocalDateTime.ofYmdHms? 2024 3 30 1 30 0
    let autumn ← LocalDateTime.ofYmdHms? 2024 10 26 2 30 0
    pure (
      ← evaluate ordinary 777 1 2,
      ← evaluate spring 333 1 1,
      ← evaluate autumn 444 1 1)) =
      some (
        ValueAsDateTimeResult.value
          ((LocalDateTime.ofYmdHms? 2024 6 17 1 30 0).get (by native_decide))
          { epochMillis := 1718580600777 } false,
        ValueAsDateTimeResult.value
          ((LocalDateTime.ofYmdHms? 2024 3 31 3 30 0).get (by native_decide))
          { epochMillis := 1711848600333 } false,
        ValueAsDateTimeResult.value
          ((LocalDateTime.ofYmdHms? 2024 10 27 2 30 0).get (by native_decide))
          { epochMillis := 1729992600444 } false) := by
  native_decide

/- Inner-before-outer order remains exact in the reverse composition. A formal day
   amount stops; day arithmetic no-value reaches a formal elapsed amount; omission
   accumulates across a value; outer arithmetic no-value remains valueless. -/
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
      (elaborateDateTimeDayShift model 1 innerField).toOption
    let stoppedInput ← input [
      { address := { field := 2, path := [] }, stored := "bad-inner",
        raw := .rejected .malformed },
      { address := { field := 3, path := [] }, stored := "0.001",
        raw := .rejected .declaredConstraint }]
    let stopped ←
      checkedField.evaluateThenSubday .hours outerField
        .computation stoppedInput |>.toOption
    let innerDomain ←
      (elaborateValueAsDateTimeExpressionShiftAmount
        model ["Order"] innerAmountOverZero).toOption
    let checkedDomain ←
      (elaborateDateTimeDayShift model 1 innerDomain).toOption
    let reachedInput ← input [
      { address := { field := 2, path := [] }, stored := "3",
        raw := .parsed (.num 3) },
      { address := { field := 3, path := [] }, stored := "0.001",
        raw := .rejected .declaredConstraint }]
    let reached ←
      checkedDomain.evaluateThenSubday .hours outerField
        .computation reachedInput |>.toOption
    let omittedInput ← input []
    let omitted ←
      checkedField.evaluateThenSubday .hours (.literal 1)
        .computation omittedInput |>.toOption
    let fixed ←
      (elaborateDateTimeDayShift model 1 (.literal 0)).toOption
    let domainInput ← input [{
      address := { field := 2, path := [] }, stored := "3",
      raw := .parsed (.num 3) }]
    let outerDomain ←
      fixed.evaluateThenSubday .hours innerDomain
        .computation domainInput |>.toOption
    pure (stopped, reached, omitted, outerDomain)) =
      some (
        ValueAsDateTimeResult.unavailable .malformed,
        ValueAsDateTimeResult.unavailable .declaredConstraint,
        ValueAsDateTimeResult.value
          ((LocalDateTime.ofYmdHms? 2024 6 15 11 30 0).get (by native_decide))
          { epochMillis := 1718443800000 } true,
        ValueAsDateTimeResult.noValue false) := by
  native_decide

/- Dynamic calendar mutation consumes each supplied world first; elapsed arithmetic
   then preserves the exact ordinary, spring-gap, and autumn-overlap landings. -/
example : (do
    let input ← document? []
    let evaluate (sourceLabel : LocalDateTime) (millisecond : Int)
        (days hours : Rat) := do
      let resolved ←
        ModelZone.ConcreteProfile.europeBerlin.resolveLocal? sourceLabel
      let world : World := {
        now := { epochMillis := resolved.epochMillis + millisecond }
      }
      let checked ←
        (elaborateNowDateTimeDayShift model (.literal days)).toOption
      checked.evaluateThenSubday .hours (.literal hours)
        .computation world input |>.toOption
    let ordinary ← LocalDateTime.ofYmdHms? 2024 6 15 23 30 0
    let spring ← LocalDateTime.ofYmdHms? 2024 3 30 1 30 0
    let autumn ← LocalDateTime.ofYmdHms? 2024 10 26 2 30 0
    pure (
      ← evaluate ordinary 777 1 2,
      ← evaluate spring 333 1 1,
      ← evaluate autumn 444 1 1)) =
      some (
        ValueAsDateTimeResult.value
          ((LocalDateTime.ofYmdHms? 2024 6 17 1 30 0).get (by native_decide))
          { epochMillis := 1718580600777 } false,
        ValueAsDateTimeResult.value
          ((LocalDateTime.ofYmdHms? 2024 3 31 3 30 0).get (by native_decide))
          { epochMillis := 1711848600333 } false,
        ValueAsDateTimeResult.value
          ((LocalDateTime.ofYmdHms? 2024 10 27 2 30 0).get (by native_decide))
          { epochMillis := 1729992600444 } false) := by
  native_decide

/- Dynamic reverse composition retains the same inner-before-outer cause and omission
   order without merging its checked carrier with field-backed execution. -/
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
      (elaborateNowDateTimeDayShift model innerField).toOption
    let stoppedInput ← document? [
      { address := { field := 2, path := [] }, stored := "bad-inner",
        raw := .rejected .malformed },
      { address := { field := 3, path := [] }, stored := "0.001",
        raw := .rejected .declaredConstraint }]
    let stopped ←
      checkedField.evaluateThenSubday .hours outerField
        .computation world stoppedInput |>.toOption
    let innerDomain ←
      (elaborateValueAsDateTimeExpressionShiftAmount
        model ["Order"] innerAmountOverZero).toOption
    let checkedDomain ←
      (elaborateNowDateTimeDayShift model innerDomain).toOption
    let reachedInput ← document? [
      { address := { field := 2, path := [] }, stored := "3",
        raw := .parsed (.num 3) },
      { address := { field := 3, path := [] }, stored := "0.001",
        raw := .rejected .declaredConstraint }]
    let reached ←
      checkedDomain.evaluateThenSubday .hours outerField
        .computation world reachedInput |>.toOption
    let omittedInput ← document? []
    let omitted ←
      checkedField.evaluateThenSubday .hours (.literal 1)
        .computation world omittedInput |>.toOption
    let fixed ←
      (elaborateNowDateTimeDayShift model (.literal 0)).toOption
    let domainInput ← document? [{
      address := { field := 2, path := [] }, stored := "3",
      raw := .parsed (.num 3) }]
    let outerDomain ←
      fixed.evaluateThenSubday .hours innerDomain
        .computation world domainInput |>.toOption
    pure (stopped, reached, omitted, outerDomain)) =
      some (
        ValueAsDateTimeResult.unavailable .malformed,
        ValueAsDateTimeResult.unavailable .declaredConstraint,
        ValueAsDateTimeResult.value
          ((LocalDateTime.ofYmdHms? 2024 6 15 11 30 0).get (by native_decide))
          { epochMillis := 1718443800000 } true,
        ValueAsDateTimeResult.noValue false) := by
  native_decide

end A12Kernel.Conformance.DateTimeDayThenSubdayShiftEvaluation
