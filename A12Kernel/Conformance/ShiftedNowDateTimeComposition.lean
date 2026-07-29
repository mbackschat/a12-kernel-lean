import A12Kernel.Elaboration.ValueAsDateTimeExtraction

/-! # Dynamic `Now` sub-day composition locks -/

namespace A12Kernel.Conformance.ShiftedNowDateTimeComposition

open A12Kernel

private def shiftAmount : FlatFieldDecl := {
  id := 2
  groupPath := ["Order"]
  name := "ShiftAmount"
  policy := { kind := .number { scale := 2, signed := true } } }

private def outerShiftAmount : FlatFieldDecl := {
  id := 3
  groupPath := ["Order"]
  name := "OuterShiftAmount"
  policy := { kind := .number { scale := 2, signed := true } } }

private def shiftAmountPath : SurfaceFieldPath := {
  base := .absolute
  groups := ["Order"]
  field := "ShiftAmount" }

private def shiftedByFieldOverZero : AuthoredNumericExpr SurfaceNumericAtom :=
  .binary .divide
    (.atom (.field shiftAmountPath))
    (.literal { value := 0, authoredScale := 0 })

private def model : FlatModel := {
  fields := [shiftAmount, outerShiftAmount]
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

/- A dynamic source samples each supplied world exactly once, then composes cross-unit
   shifts without losing millisecond identity or re-resolving an overlap label. -/
example : (do
    let input ← document? []
    let ordinaryLocal ← LocalDateTime.ofYmdHms? 2024 6 15 23 59 30
    let ordinaryResolved ←
      ModelZone.ConcreteProfile.europeBerlin.resolveLocal? ordinaryLocal
    let ordinary : World := {
      now := { epochMillis := ordinaryResolved.epochMillis + 777 }
    }
    let overlapLocal ← LocalDateTime.ofYmdHms? 2024 10 27 1 30 0
    let overlapInstant ←
      ModelZone.ConcreteProfile.europeBerlin.resolveLocal? overlapLocal
    let overlap : World := { now := overlapInstant }
    let checked ←
      (elaborateShiftedNowDateTimeSource model
        .hours (.literal 1)).toOption
    let ordinaryResult ←
      checked.evaluateThen .minutes (.literal 2)
        .computation ordinary input |>.toOption
    let overlapResult ←
      checked.evaluateThen .seconds (.literal 0)
        .computation overlap input |>.toOption
    pure (ordinaryResult, overlapResult)) =
      some (
        ValueAsDateTimeResult.value
          ((LocalDateTime.ofYmdHms? 2024 6 16 1 1 30).get (by native_decide))
          { epochMillis := 1718492490777 } false,
        ValueAsDateTimeResult.value
          ((LocalDateTime.ofYmdHms? 2024 10 27 2 30 0).get (by native_decide))
          { epochMillis := 1729989000000 } false) := by
  native_decide

/- Dynamic nested evaluation retains inner-before-outer order. Inner arithmetic
   no-value reaches a formal outer amount; a formal inner amount stops it; omission
   accumulates across the value path; outer arithmetic no-value stays valueless. -/
example : (do
    let input (cells : List ClassifiedCellInput) := document? cells
    let nowLocal ← LocalDateTime.ofYmdHms? 2024 6 15 10 30 0
    let nowInstant ←
      ModelZone.ConcreteProfile.europeBerlin.resolveLocal? nowLocal
    let world : World := { now := nowInstant }
    let innerDomain ←
      (elaborateValueAsDateTimeExpressionShiftAmount
        model ["Order"] shiftedByFieldOverZero).toOption
    let outerField ←
      (elaborateValueAsDateTimeFieldShiftAmount model 3).toOption
    let domainFirst ←
      (elaborateShiftedNowDateTimeSource model .seconds innerDomain).toOption
    let reachedInput ← input [
      { address := { field := 2, path := [] }, stored := "3",
        raw := .parsed (.num 3) },
      { address := { field := 3, path := [] }, stored := "bad-outer",
        raw := .rejected .declaredConstraint }]
    let reached ←
      domainFirst.evaluateThen .seconds outerField
        .computation world reachedInput |>.toOption
    let innerField ←
      (elaborateValueAsDateTimeFieldShiftAmount model 2).toOption
    let fieldFirst ←
      (elaborateShiftedNowDateTimeSource model .seconds innerField).toOption
    let stoppedInput ← input [
      { address := { field := 2, path := [] }, stored := "bad-inner",
        raw := .rejected .malformed },
      { address := { field := 3, path := [] }, stored := "bad-outer",
        raw := .rejected .declaredConstraint }]
    let stopped ←
      fieldFirst.evaluateThen .seconds outerField
        .computation world stoppedInput |>.toOption
    let omittedInput ← input []
    let omitted ←
      fieldFirst.evaluateThen .seconds (.literal 1)
        .computation world omittedInput |>.toOption
    let fixed ←
      (elaborateShiftedNowDateTimeSource model
        .seconds (.literal 0)).toOption
    let domainInput ← input [{
      address := { field := 2, path := [] }, stored := "3",
      raw := .parsed (.num 3) }]
    let outerDomain ←
      fixed.evaluateThen .seconds innerDomain
        .computation world domainInput |>.toOption
    pure (reached, stopped, omitted, outerDomain)) =
      some (
        ValueAsDateTimeResult.unavailable .declaredConstraint,
        ValueAsDateTimeResult.unavailable .malformed,
        ValueAsDateTimeResult.value
          ((LocalDateTime.ofYmdHms? 2024 6 15 10 30 1).get (by native_decide))
          { epochMillis := 1718440201000 } true,
        ValueAsDateTimeResult.noValue false) := by
  native_decide

end A12Kernel.Conformance.ShiftedNowDateTimeComposition
