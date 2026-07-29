import A12Kernel.Elaboration.DateTimeDayShiftEvaluation

/-! # Dynamic `Now` calendar-day shift locks -/

namespace A12Kernel.Conformance.DateTimeNowDayShiftEvaluation

open A12Kernel

private def amount : FlatFieldDecl := {
  id := 1
  groupPath := ["Order"]
  name := "Days"
  policy := { kind := .number { scale := 2, signed := true } } }

private def nextAmount : FlatFieldDecl := {
  id := 2
  groupPath := ["Order"]
  name := "MoreDays"
  policy := { kind := .number { scale := 2, signed := true } } }

private def amountPath : SurfaceFieldPath := {
  base := .absolute
  groups := ["Order"]
  field := "Days" }

private def amountOverZero : AuthoredNumericExpr SurfaceNumericAtom :=
  .binary .divide
    (.atom (.field amountPath))
    (.literal { value := 0, authoredScale := 0 })

private def model : FlatModel := {
  fields := [amount, nextAmount]
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

/- Each call consumes its supplied world's exact instant. Long-range forward and
   reverse landings retain the world's source offset and millisecond component. -/
example : (do
    let input ← document? []
    let evaluate (sourceLabel : LocalDateTime) (millisecond : Int)
        (days : Rat) := do
      let resolved ←
        ModelZone.ConcreteProfile.europeBerlin.resolveLocal? sourceLabel
      let world : World := {
        now := { epochMillis := resolved.epochMillis + millisecond }
      }
      let checked ←
        (elaborateNowDateTimeDayShift model (.literal days)).toOption
      checked.evaluate .computation world input |>.toOption
    let ordinary ← LocalDateTime.ofYmdHms? 2024 6 15 10 30 0
    let forward ← LocalDateTime.ofYmdHms? 2023 8 31 2 30 0
    let reverse ← LocalDateTime.ofYmdHms? 2024 11 30 2 30 0
    pure (
      ← evaluate ordinary 444 1,
      ← evaluate forward 777 213,
      ← evaluate reverse 333 (-244))) =
      some (
        ValueAsDateTimeResult.value
          ((LocalDateTime.ofYmdHms? 2024 6 16 10 30 0).get (by native_decide))
          { epochMillis := 1718526600444 } false,
        ValueAsDateTimeResult.value
          ((LocalDateTime.ofYmdHms? 2024 3 31 3 30 0).get (by native_decide))
          { epochMillis := 1711848600777 } false,
        ValueAsDateTimeResult.value
          ((LocalDateTime.ofYmdHms? 2024 3 31 1 30 0).get (by native_decide))
          { epochMillis := 1711845000333 } false) := by
  native_decide

/- Dynamic calendar shifting reuses checked numeric semantics: fractional amounts
   truncate, empty is a concrete zero shift with omission, formal cause is retained,
   and arithmetic domain failure stays valueless. -/
example : (do
    let nowLabel ← LocalDateTime.ofYmdHms? 2024 6 15 10 30 0
    let nowInstant ←
      ModelZone.ConcreteProfile.europeBerlin.resolveLocal? nowLabel
    let world : World := { now := nowInstant }
    let fieldAmount ←
      (elaborateValueAsDateTimeFieldShiftAmount model 1).toOption
    let fieldChecked ←
      (elaborateNowDateTimeDayShift model fieldAmount).toOption
    let evaluateField (raw : Option (RawCell Value)) := do
      let input ← document? (raw.toList.map fun cell => {
        address := { field := 1, path := [] }
        stored := match cell with
          | .parsed (.num value) =>
              if value = 3 / 2 then "1.5" else toString value
          | .rejected .declaredConstraint => "0.001"
          | _ => "bad"
        raw := cell
      })
      fieldChecked.evaluate .computation world input |>.toOption
    let expressionAmount ←
      (elaborateValueAsDateTimeExpressionShiftAmount
        model ["Order"] amountOverZero).toOption
    let expressionChecked ←
      (elaborateNowDateTimeDayShift model expressionAmount).toOption
    let expressionInput ← document? [{
      address := { field := 1, path := [] }
      stored := "3"
      raw := .parsed (.num 3)
    }]
    let domain ←
      expressionChecked.evaluate .computation world expressionInput |>.toOption
    pure (
      ← evaluateField (some (.parsed (.num (3 / 2)))),
      ← evaluateField none,
      ← evaluateField (some (.rejected .declaredConstraint)),
      domain)) =
      some (
        ValueAsDateTimeResult.value
          ((LocalDateTime.ofYmdHms? 2024 6 16 10 30 0).get (by native_decide))
          { epochMillis := 1718526600000 } false,
        ValueAsDateTimeResult.value
          ((LocalDateTime.ofYmdHms? 2024 6 15 10 30 0).get (by native_decide))
          { epochMillis := 1718440200000 } true,
        ValueAsDateTimeResult.unavailable .declaredConstraint,
        ValueAsDateTimeResult.noValue false) := by
  native_decide

/- One checked dynamic two-day continuation observes each supplied world and applies
   the inner source-offset landing before the outer one. -/
example : (do
    let input ← document? []
    let operation ←
      (elaborateNowDateTimeDayShift model (.literal 1)).toOption
    let firstLocal ← LocalDateTime.ofYmdHms? 2024 6 15 10 30 0
    let secondLocal ← LocalDateTime.ofYmdHms? 2024 6 16 10 30 0
    let firstNow ←
      ModelZone.ConcreteProfile.europeBerlin.resolveLocal? firstLocal
    let secondNow ←
      ModelZone.ConcreteProfile.europeBerlin.resolveLocal? secondLocal
    let first ←
      operation.evaluateThen (.literal 1) .validation
        { now := firstNow } input |>.toOption
    let second ←
      operation.evaluateThen (.literal 1) .validation
        { now := secondNow } input |>.toOption
    pure (first, second)) =
    some (
      .value
        ((LocalDateTime.ofYmdHms? 2024 6 17 10 30 0).get (by native_decide))
        { epochMillis := 1718613000000 } false,
      .value
        ((LocalDateTime.ofYmdHms? 2024 6 18 10 30 0).get (by native_decide))
        { epochMillis := 1718699400000 } false) := by
  native_decide

/- Long-range gap mutation feeds its exact 03:30 landing to the next day, while a
   zero outer step preserves the earlier repeated-midnight instant exactly. -/
example : (do
    let input ← document? []
    let gapLocal ← LocalDateTime.ofYmdHms? 2023 8 31 2 30 0
    let gapNow ←
      ModelZone.ConcreteProfile.europeBerlin.resolveLocal? gapLocal
    let gap ←
      (elaborateNowDateTimeDayShift model (.literal 213)).toOption
    let gapResult ←
      gap.evaluateThen (.literal 1) .validation { now := gapNow } input
        |>.toOption
    let overlapLocal ← LocalDateTime.ofYmdHms? 1916 9 30 0 0 0
    let overlapNow ←
      ModelZone.ConcreteProfile.europeBerlin.resolveLocal? overlapLocal
    let overlap ←
      (elaborateNowDateTimeDayShift model (.literal 1)).toOption
    let overlapResult ←
      overlap.evaluateThen (.literal 0) .validation
        { now := overlapNow } input |>.toOption
    pure (gapResult, overlapResult)) =
    some (
      .value
        ((LocalDateTime.ofYmdHms? 2024 4 1 3 30 0).get (by native_decide))
        { epochMillis := 1711935000000 } false,
      .value
        ((LocalDateTime.ofYmdHms? 1916 10 1 0 0 0).get (by native_decide))
        { epochMillis := -1680487200000 } false) := by
  native_decide

/- Omission from either amount accumulates on the final value. An inner formal cause
   short-circuits the outer read, while cause-free inner no-value reaches it. -/
example : (do
    let nowLocal ← LocalDateTime.ofYmdHms? 2024 6 15 10 30 0
    let now ← ModelZone.ConcreteProfile.europeBerlin.resolveLocal? nowLocal
    let firstField ←
      (elaborateValueAsDateTimeFieldShiftAmount model amount.id).toOption
    let secondField ←
      (elaborateValueAsDateTimeFieldShiftAmount model nextAmount.id).toOption
    let noCells ← document? []
    let omittedFirst ←
      (elaborateNowDateTimeDayShift model firstField).toOption
    let omittedFirstResult ←
      omittedFirst.evaluateThen (.literal 1) .computation { now } noCells
        |>.toOption
    let omittedSecond ←
      (elaborateNowDateTimeDayShift model (.literal 1)).toOption
    let omittedSecondResult ←
      omittedSecond.evaluateThen secondField .computation { now } noCells
        |>.toOption
    let badInput ← document? [
      { address := { field := amount.id, path := [] }
        stored := "bad-first"
        raw := .rejected .malformed },
      { address := { field := nextAmount.id, path := [] }
        stored := "0.001"
        raw := .rejected .declaredConstraint }]
    let badInner ←
      (elaborateNowDateTimeDayShift model firstField).toOption
    let badInnerResult ←
      badInner.evaluateThen secondField .computation { now } badInput
        |>.toOption
    let domainAmount ←
      (elaborateValueAsDateTimeExpressionShiftAmount model ["Order"]
        amountOverZero).toOption
    let domainInner ←
      (elaborateNowDateTimeDayShift model domainAmount).toOption
    let domainInput ← document? [
      { address := { field := amount.id, path := [] }
        stored := "1"
        raw := .parsed (.num 1) },
      { address := { field := nextAmount.id, path := [] }
        stored := "0.001"
        raw := .rejected .declaredConstraint }]
    let domainResult ←
      domainInner.evaluateThen secondField .computation { now } domainInput
        |>.toOption
    pure (omittedFirstResult, omittedSecondResult,
      badInnerResult, domainResult)) =
    some (
      .value
        ((LocalDateTime.ofYmdHms? 2024 6 16 10 30 0).get (by native_decide))
        { epochMillis := 1718526600000 } true,
      .value
        ((LocalDateTime.ofYmdHms? 2024 6 16 10 30 0).get (by native_decide))
        { epochMillis := 1718526600000 } true,
      .unavailable .malformed,
      .unavailable .declaredConstraint) := by
  native_decide

end A12Kernel.Conformance.DateTimeNowDayShiftEvaluation
