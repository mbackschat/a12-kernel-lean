import A12Kernel.Elaboration.TimeComputation

/-! # Checked `Time(...)` target locks -/

namespace A12Kernel.Conformance.TimeComputation

open A12Kernel

private def clock (hour minute second : Nat)
    (valid : hour < 24 ∧ minute < 60 ∧ second < 60) : TimeOfDay :=
  ⟨hour, minute, second, valid⟩

private def components : TemporalComponents := TemporalComponents.time

private def target (format : String := "HH:mm:ss")
    (actualComponents : TemporalComponents := components) :
    FlatFieldDecl := {
  id := 1
  groupPath := ["Order"]
  name := "CalculatedTime"
  policy := { kind := .temporal .time actualComponents }
  temporalTargetPolicy := some { format } }

private def model (zoneId : String := "UTC") : FlatModel := {
  fields := [target]
  timeZoneId := zoneId }

private def timeTargetError? (candidate : FlatModel) :
    Option TimeTargetElabError :=
  match elaborateTimeTarget candidate 1 with
  | .ok _ => none
  | .error error => some error

private def evaluate? (candidate : FlatModel)
    (result : TimeConstructionResult) : Option TimeTargetOutcome := do
  let checked ← (elaborateTimeTarget candidate 1).toOption
  pure (checked.evaluate result.asTimeComputationResult)

private def nextTime : StoredTime := ⟨"05:02:09", by decide⟩

/- Exact complete Time is admitted; component or format widening fails before execution. -/
example :
    timeTargetError? (model) = none ∧
      timeTargetError? { fields := [target "HH:mm"] } =
        some (.unsupportedFormat 1 "HH:mm") ∧
      let missingSecond := { components with second := false }
      timeTargetError? { fields := [target "HH:mm:ss" missingSecond] } =
        some (.components 1 missingSecond) := by
  native_decide

/- Time rendering retains the clock exactly and never consults the model zone. -/
example :
    let value := TimeConstructionResult.value (clock 5 2 9 (by decide))
    evaluate? (model "UTC") value = some (.accepted nextTime) ∧
      evaluate? (model "Europe/Berlin") value =
        some (.accepted nextTime) := by
  native_decide

/- Missing, impossible, and non-relevant constructions are quiet no-value; formal unavailability is poison. -/
example :
    let checked := (elaborateTimeTarget (model) 1).toOption.get
      (by native_decide)
    ([ .incomplete, .unreal, .nonRelevant ] :
      List TimeConstructionResult).map
        (fun result => checked.evaluate result.asTimeComputationResult) =
      [.noValue, .noValue, .noValue] ∧
      checked.evaluate
        (TimeConstructionResult.unavailable .malformed).asTimeComputationResult =
        .poison .malformed := by
  native_decide

end A12Kernel.Conformance.TimeComputation
