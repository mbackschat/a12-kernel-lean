import A12Kernel.Elaboration.DateTimeComputation

/-! # Checked `Now` DateTime computation locks -/

namespace A12Kernel.Conformance.DateTimeComputation

open A12Kernel

private def targetFor (format : String) : FlatFieldDecl := {
  id := 1
  groupPath := ["Order"]
  name := "CalculatedAt"
  policy := {
    kind := .temporal .dateTime TemporalComponents.now }
  temporalTargetPolicy := some {
    format
    partialMode := .full } }

private def amount : FlatFieldDecl := {
  id := 2
  groupPath := ["Order"]
  name := "Offset"
  policy := { kind := .number { scale := 0, signed := true } } }

private def modelFor (format : String) : FlatModel := {
  fields := [targetFor format, amount]
  timeZoneId := "UTC" }

private def preparedFor? (format : String) :=
  (prepareFlatStringContext { now := { epochMillis := 0 } }
    builtinStringPatternCompiler (modelFor format)).toOption

private def inputFor? (format : String)
    (amountRaw : RawCell := .parsed (.num 0))
    (targetStored : String := "old") :
    Option (CheckedDocument (modelFor format)) := do
  let prepared ← preparedFor? format
  let targetLocal ← LocalDateTime.ofYmdHms? 1970 1 1 0 0 0
  checkDocument prepared "en_US" {
    instantiatedRows := []
    cells := [
      { address := { field := amount.id, path := [] }
        stored := match amountRaw with
          | .parsed (.num value) => toString value
          | .rejected .declaredConstraint => "0.1"
          | .presentEmpty => ""
          | _ => "bad"
        raw := amountRaw },
      { address := { field := (targetFor format).id, path := [] }
        stored := targetStored
        raw := .parsed (.temporal (.dateTime { epochMillis := 0 }
          targetLocal.date.civil.parts targetLocal.time .storedGregorian)) }
    ]
  } |>.toOption

private def instant? (year : Int) (month day hour minute second : Nat)
    (millisecond : Nat := 0) : Option Instant :=
  (LocalDateTime.ofYmdHms? year month day hour minute second).map
    fun dateTime =>
      { epochMillis :=
          dateTime.resolveUtc.epochMillis + millisecond }

private def outcomeAt? (now : Instant) :
    Option DateTimeTargetOutcome := do
  let operation ←
    (elaborateDateTimeNowComputation
      (modelFor "yyyy-MM-dd'T'HH:mm:ss") 1).toOption
  operation.evaluateOutcome { now } |>.toOption

private def errorOf
    (result : Except DateTimeComputationElabError value) :
    Option DateTimeComputationElabError :=
  match result with
  | .ok _ => none
  | .error error => some error

/- The checked operation retains the existing `Now` operand and transports the world's exact instant to whole-second target text. -/
example : (do
    let now ← instant? 2025 6 23 10 0 0 999
    let operation ←
      (elaborateDateTimeNowComputation
        (modelFor "yyyy-MM-dd'T'HH:mm:ss") 1).toOption
    let outcome ← operation.evaluateOutcome { now } |>.toOption
    pure (operation.operand, outcome)) =
    some (.nowValue, .accepted {
      text := "2025-06-23T10:00:00"
      nonempty := by decide }) := by
  native_decide

/- Stored DateTime text cannot recover the millisecond remainder: two distinct execution worlds inside one second produce the same result. -/
example : (do
    let first ← instant? 2025 6 23 10 0 0 1
    let second ← instant? 2025 6 23 10 0 0 999
    let firstOutcome ← outcomeAt? first
    let secondOutcome ← outcomeAt? second
    pure (first ≠ second, firstOutcome = secondOutcome)) =
      some (true, true) := by
  native_decide

/- A separately sampled later world can cross the stored-second boundary. Calculation and later generated validation must not be assumed to share a sample. -/
example : (do
    let calculation ← instant? 2025 6 23 10 0 0 999
    let laterValidation ← instant? 2025 6 23 10 0 1
    let calculated ← outcomeAt? calculation
    let later ← outcomeAt? laterValidation
    pure (calculated, later, calculated ≠ later)) =
    some (
      .accepted {
        text := "2025-06-23T10:00:00"
        nonempty := by decide },
      .accepted {
        text := "2025-06-23T10:00:01"
        nonempty := by decide },
      true) := by
  native_decide

/- Unsupported target syntax is rejected by the existing DateTime target certificate before any world is observed. -/
example :
    errorOf (elaborateDateTimeNowComputation
      (modelFor "yyyy/MM/dd'T'HH:mm:ss") 1) =
      some (.target
        (.unsupportedFormat 1 "yyyy/MM/dd'T'HH:mm:ss")) := by
  native_decide

/- All three dynamic sub-day shifts sample this call's exact world once, preserve
   milliseconds and calendar carry, then delegate whole-second target rendering. -/
example : (do
    let now ← instant? 2025 6 23 23 59 30 777
    let input ← inputFor? "yyyy-MM-dd'T'HH:mm:ss"
    let evaluate (unit : DateTimeSubdayUnit) (value : Rat) := do
      let operation ←
        (elaborateShiftedNowDateTimeComputation
          (modelFor "yyyy-MM-dd'T'HH:mm:ss")
          unit (.literal value) 1).toOption
      let operand ← operation.evaluateOperand { now } input |>.toOption
      let outcome ← operation.evaluateOutcome { now } input |>.toOption
      pure (operand, outcome)
    let hours ← evaluate .hours 2
    let minutes ← evaluate .minutes 2
    let seconds ← evaluate .seconds 45
    pure (hours, minutes, seconds)) =
      some (
        (.value { epochMillis := 1750730370777 },
          .accepted ⟨"2025-06-24T01:59:30", by decide⟩),
        (.value { epochMillis := 1750723290777 },
          .accepted ⟨"2025-06-24T00:01:30", by decide⟩),
        (.value { epochMillis := 1750723215777 },
          .accepted ⟨"2025-06-24T00:00:15", by decide⟩)) := by
  native_decide

/- Elaboration retains no instant: one checked shifted-Now operation transports two
   distinct execution worlds to two distinct exact target values. -/
example : (do
    let first ← instant? 2025 6 23 10 0 0 1
    let second ← instant? 2025 6 23 10 0 1 999
    let input ← inputFor? "yyyy-MM-dd'T'HH:mm:ss"
    let operation ←
      (elaborateShiftedNowDateTimeComputation
        (modelFor "yyyy-MM-dd'T'HH:mm:ss")
        .seconds (.literal 1) 1).toOption
    let firstResult ← operation.evaluateOperand { now := first } input |>.toOption
    let secondResult ← operation.evaluateOperand { now := second } input |>.toOption
    pure (firstResult, secondResult, firstResult ≠ secondResult)) =
      some (
        .value { epochMillis := 1750672801001 },
        .value { epochMillis := 1750672802999 },
        true) := by
  native_decide

/- A reached formal amount remains target poison; arithmetic domain failure remains
   clean no-value and clears a source-filled target instead of becoming a zero shift. -/
example : (do
    let now ← instant? 2025 6 23 10 0 0
    let poisonedInput ←
      inputFor? "yyyy-MM-dd'T'HH:mm:ss" (.rejected .declaredConstraint)
    let checkedAmount ←
      (elaborateValueAsDateTimeFieldShiftAmount
        (modelFor "yyyy-MM-dd'T'HH:mm:ss") amount.id).toOption
    let poisoned ←
      (elaborateShiftedNowDateTimeComputation
        (modelFor "yyyy-MM-dd'T'HH:mm:ss")
        .seconds checkedAmount 1).toOption
    let poisonOutcome ←
      poisoned.evaluateOutcome { now } poisonedInput |>.toOption
    let unavailable ←
      (elaborateValueAsDateTimeExpressionShiftAmount
        (modelFor "yyyy-MM-dd'T'HH:mm:ss") ["Order"]
        (.binary .divide
          (.literal { value := 1, authoredScale := 0 })
          (.literal { value := 0, authoredScale := 0 }))).toOption
    let empty ←
      (elaborateShiftedNowDateTimeComputation
        (modelFor "yyyy-MM-dd'T'HH:mm:ss")
        .seconds unavailable 1).toOption
    let view ←
      empty.executeResult { now } poisonedInput ([] : List FormalCause)
        |>.toOption
    pure (poisonOutcome, view.cleared, view.withoutErrors)) =
      some (.poison .declaredConstraint, [1], []) := by
  native_decide

/- Successful shifted-Now target text reaches source-relative application unchanged. -/
example : (do
    let now ← instant? 2025 6 23 10 0 0 777
    let input ← inputFor? "yyyy-MM-dd'T'HH:mm:ss"
    let operation ←
      (elaborateShiftedNowDateTimeComputation
        (modelFor "yyyy-MM-dd'T'HH:mm:ss")
        .minutes (.literal 1) 1).toOption
    let view ← operation.executeResult { now } input ([] : List FormalCause)
      |>.toOption
    let applied ← view.applyTo (fun _ => .absent) |>.toOption
    pure (view.withChanges.map (·.value.text), applied 1)) =
      some (["2025-06-23T10:01:00"],
        .presentValue ⟨"2025-06-23T10:01:00", by decide⟩) := by
  native_decide

end A12Kernel.Conformance.DateTimeComputation
