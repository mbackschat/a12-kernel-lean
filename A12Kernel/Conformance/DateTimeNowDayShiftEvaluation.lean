import A12Kernel.Elaboration.DateTimeDayShiftEvaluation

/-! # Dynamic `Now` calendar-day shift locks -/

namespace A12Kernel.Conformance.DateTimeNowDayShiftEvaluation

open A12Kernel

private def amount : FlatFieldDecl := {
  id := 1
  groupPath := ["Order"]
  name := "Days"
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
  fields := [amount]
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
        stored := "amount"
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

end A12Kernel.Conformance.DateTimeNowDayShiftEvaluation
