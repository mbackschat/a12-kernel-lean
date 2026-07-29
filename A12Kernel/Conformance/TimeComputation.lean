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

private def oldTime : StoredTime := ⟨"05:02:08", by decide⟩

private def source (stored : String) (raw : RawCell) : DocumentData := {
  instantiatedRows := []
  cells := [{ address := { field := 1, path := [] }, stored, raw }] }

private def oldSource : DocumentData :=
  source oldTime.text (.parsed (.temporal
    (.time { epochMillis := 0 } (clock 5 2 8 (by decide)))))

private def prepared :=
  (prepareFlatStringContext { now := { epochMillis := 0 } }
    builtinStringPatternCompiler (model)).toOption.get (by native_decide)

private def view? (input : DocumentData) (outcome : TimeTargetOutcome)
    (messages : List FormalCause := []) :
    Option (TimeComputationRunView FormalCause) := do
  let checked ← (checkDocument prepared "en_US" input).toOption
  pure (TimeComputationRunView.fromOutcomes checked messages [(1, outcome)])

private def destinationWith (state : TimeTargetState) :
    TimeComputationDestination :=
  fun field => if field == 1 then state else .absent

private def componentField (id : FieldId) : FlatFieldDecl := {
  id
  groupPath := ["Order"]
  name := s!"Component{id}"
  policy := { kind := .number { scale := 0, signed := false } }
  numericTargetConstraints := { maxStoredLength := some 2 } }

private def executionModel : FlatModel := {
  fields := [target, componentField 2, componentField 3, componentField 4]
  timeZoneId := "UTC" }

private def componentCell (field : FieldId) (stored : String)
    (raw : RawCell) : ClassifiedCellInput := {
  address := { field, path := [] }
  stored
  raw }

private def executionSource
    (components : List ClassifiedCellInput) : DocumentData := {
  oldSource with cells := oldSource.cells ++ components }

private def operation? (components : SurfaceTimeComponents) :
    Option (CheckedTimeConstructionComputation executionModel) :=
  (elaborateTimeConstructionComputation executionModel components 1).toOption

private def operationError? (components : SurfaceTimeComponents) :
    Option TimeConstructionComputationElabError :=
  match elaborateTimeConstructionComputation executionModel components 1 with
  | .error error => some error
  | .ok _ => none

private def executionView? (components : SurfaceTimeComponents)
    (input : DocumentData) :
    Option (TimeComputationRunView FormalCause) := do
  let operation ← operation? components
  let prepared ←
    (prepareFlatStringContext { now := { epochMillis := 0 } }
      builtinStringPatternCompiler executionModel).toOption
  let checked ← (checkDocument prepared "en_US" input).toOption
  operation.executeResult checked [] |>.toOption

private def executionOutcome? (components : SurfaceTimeComponents)
    (input : DocumentData) : Option TimeTargetOutcome := do
  let operation ← operation? components
  let prepared ←
    (prepareFlatStringContext { now := { epochMillis := 0 } }
      builtinStringPatternCompiler executionModel).toOption
  let checked ← (checkDocument prepared "en_US" input).toOption
  operation.evaluateOutcome checked |>.toOption

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

/- Unchanged success stays public but is not a change; changed success is in both projections. -/
example :
    (view? oldSource (.accepted oldTime)).map
        (fun view => (view.withoutErrors, view.withChanges)) =
      some ([{ targetField := 1, value := oldTime }], []) ∧
    (view? oldSource (.accepted nextTime)).map
        (fun view => (view.withoutErrors, view.withChanges)) =
      some ([{ targetField := 1, value := nextTime }],
        [{ targetField := 1, value := nextTime }]) := by
  native_decide

/- Quiet no-value and poison clear only a source-filled target and manufacture no target-local error. -/
example :
    (view? oldSource .noValue).map
        (fun view => (view.cleared, view.withErrors)) = some ([1], []) ∧
      (view? { instantiatedRows := [], cells := [] } .noValue).map
        (·.cleared) = some [] ∧
      (view? (source "" .presentEmpty) .noValue).map
        (·.cleared) = some [] ∧
      (view? oldSource (.poison .malformed)).map
        (fun view => (view.cleared, view.noErrorOccurred)) =
          some ([1], true) := by
  native_decide

/- Application writes changed text, clears a filled target in place, and ignores residual messages. -/
example :
    (do
      let view ← view? oldSource (.accepted nextTime) [.malformed]
      let applied ← view.applyTo (destinationWith .absent) |>.toOption
      pure (applied 1, view.noErrorOccurred)) =
        some (.presentValue nextTime, false) ∧
      (do
        let view ← view? oldSource .noValue
        let applied ← view.applyTo
          (destinationWith (.presentValue nextTime)) |>.toOption
        pure (applied 1)) = some .presentEmpty := by
  native_decide

/- A duplicate clear/write target is rejected before destination state participates. -/
example :
    (do
      let checked ← (checkDocument prepared "en_US" oldSource).toOption
      let view := TimeComputationRunView.fromOutcomes checked
        ([] : List FormalCause)
        [(1, .noValue), (1, .accepted nextTime)]
      pure (match view.applyTo (destinationWith .absent) with
        | .error error => some error
        | .ok _ => none)) =
        some (some (.duplicateActionTarget 1)) := by
  native_decide

/- A checked mixed prefix is admitted, while a matching extractor from the Time target is rejected before execution. -/
example :
    (operation? (.second
      (.number 2) (.number 3) (.number 4))).isSome = true ∧
      operationError? (.hour (.extractor .hour 1)) =
        some (.targetSelfReference 1) := by
  native_decide

/- One checked component defaults the omitted suffix to zero and flows through source-relative result classification. -/
example :
    (executionView? (.hour (.number 2))
      (executionSource [
        componentCell 2 "05" (.parsed (.num 5))])).map
      (fun view => (view.withoutErrors, view.withChanges)) =
        some ([{ targetField := 1, value := ⟨"05:00:00", by decide⟩ }],
          [{ targetField := 1, value := ⟨"05:00:00", by decide⟩ }]) := by
  native_decide

/- The complete prefix reads in generated order; the first reached formal cause wins and clears a source-filled target without manufacturing an error. -/
example :
    executionOutcome? (.second
      (.number 2) (.number 3) (.number 4))
      (executionSource [
        componentCell 2 "bad" (.rejected .malformed),
        componentCell 3 "100" (.rejected .declaredConstraint)]) =
        some (.poison .malformed) ∧
      (executionView? (.second
      (.number 2) (.number 3) (.number 4))
      (executionSource [
        componentCell 2 "bad" (.rejected .malformed),
        componentCell 3 "100" (.rejected .declaredConstraint)])).map
      (fun view => (view.cleared, view.withErrors, view.noErrorOccurred)) =
        some ([1], [], true) := by
  native_decide

/- A fully present impossible clock is quiet no-value, while a valid complete clock reaches exact application. -/
example :
    (executionView? (.second
      (.number 2) (.number 3) (.number 4))
      (executionSource [
        componentCell 2 "25" (.parsed (.num 25)),
        componentCell 3 "00" (.parsed (.num 0)),
        componentCell 4 "00" (.parsed (.num 0))])).map
      (·.cleared) = some [1] ∧
      (do
        let view ← executionView? (.second
          (.number 2) (.number 3) (.number 4))
          (executionSource [
            componentCell 2 "05" (.parsed (.num 5)),
            componentCell 3 "02" (.parsed (.num 2)),
            componentCell 4 "09" (.parsed (.num 9))])
        let applied ← view.applyTo (destinationWith .absent) |>.toOption
        pure (applied 1)) = some (.presentValue nextTime) := by
  native_decide

end A12Kernel.Conformance.TimeComputation
