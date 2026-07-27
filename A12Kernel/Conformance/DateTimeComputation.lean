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

private def modelFor (format : String) : FlatModel := {
  fields := [targetFor format]
  timeZoneId := "UTC" }

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
      (modelFor "dd.MM.yyyy'T'HH:mm:ss") 1).toOption
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
        (modelFor "dd.MM.yyyy'T'HH:mm:ss") 1).toOption
    let outcome ← operation.evaluateOutcome { now } |>.toOption
    pure (operation.operand, outcome)) =
    some (.nowValue, .accepted {
      text := "23.06.2025T10:00:00"
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
        text := "23.06.2025T10:00:00"
        nonempty := by decide },
      .accepted {
        text := "23.06.2025T10:00:01"
        nonempty := by decide },
      true) := by
  native_decide

/- Unsupported target syntax is rejected by the existing DateTime target certificate before any world is observed. -/
example :
    errorOf (elaborateDateTimeNowComputation
      (modelFor "yyyy-MM-dd'T'HH:mm:ss") 1) =
      some (.target
        (.unsupportedFormat 1 "yyyy-MM-dd'T'HH:mm:ss")) := by
  native_decide

end A12Kernel.Conformance.DateTimeComputation
