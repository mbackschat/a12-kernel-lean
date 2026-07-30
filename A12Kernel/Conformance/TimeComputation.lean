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
  numericTargetConstraints := {
    maxStoredLength := some 2
    leadingZerosAllowed := true
  } }

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

private def executionDocument? (input : DocumentData) :
    Option (CheckedDocument executionModel) := do
  let prepared ←
    (prepareFlatStringContext { now := { epochMillis := 0 } }
      builtinStringPatternCompiler executionModel).toOption
  (checkDocument prepared "en_US" input).toOption

private def worldLiteralOperation? (amount : Rat := 0) :
    Option (CheckedWorldTimeConstructionComputation executionModel) := do
  let component ←
    (elaborateNowShiftedTimeExtractorLiteral executionModel
      .hour .hour .hours amount).toOption
  (certifyWorldTimeConstructionComputation executionModel
    (.hour component) 1).toOption

private def worldFieldOperation? (amountField : FieldId := 2) :
    Option (CheckedWorldTimeConstructionComputation executionModel) := do
  let amount ←
    (elaborateTemporalFieldShiftAmount executionModel amountField).toOption
  let component ←
    (elaborateNowShiftedTimeExtractor executionModel
      .hour .hour .hours amount).toOption
  (certifyWorldTimeConstructionComputation executionModel
    (.hour component) 1).toOption

private def worldOutcome? (operation :
    CheckedWorldTimeConstructionComputation executionModel)
    (world : World) (input : DocumentData) : Option TimeTargetOutcome := do
  let checked ← executionDocument? input
  operation.evaluateOutcome world checked |>.toOption

private def worldView? (operation :
    CheckedWorldTimeConstructionComputation executionModel)
    (world : World) (input : DocumentData) :
    Option (TimeComputationRunView FormalCause) := do
  let checked ← executionDocument? input
  operation.executeResult world checked [] |>.toOption

private def worldSelfReferenceError? :
    Option WorldTimeConstructionComputationElabError := do
  let static ←
    (elaborateTimeComponents executionModel
      (.hour (.extractor .hour 1))).toOption
  match certifyWorldTimeConstructionComputation executionModel
      static.toWorld 1 with
  | .error error => some error
  | .ok _ => none

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

/- Kernel 30.8.1 reports every clean computed Time in the changed subset, including source-identical text. -/
example :
    (view? oldSource (.accepted oldTime)).map
        (fun view => (view.withoutErrors, view.withChanges)) =
      some ([{ targetField := 1, value := oldTime }],
        [{ targetField := 1, value := oldTime }]) ∧
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

/- Source-identical Time remains an application action and overwrites a different destination clock. -/
example :
    (do
      let view ← view? oldSource (.accepted oldTime)
      let applied ←
        view.applyTo (destinationWith (.presentValue nextTime)) |>.toOption
      pure (view.withChanges, applied 1)) =
      some ([{ targetField := 1, value := oldTime }],
        .presentValue oldTime) := by
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

/- The zero-argument form is real midnight; one and two constants supply fixed trailing zeroes and reach the same target path. -/
example :
    (executionView? .empty oldSource).map (·.withChanges) =
        some [{ targetField := 1, value := ⟨"00:00:00", by decide⟩ }] ∧
      (executionView? (.hour (.constant "10")) oldSource).map
        (·.withoutErrors) =
          some [{ targetField := 1, value := ⟨"10:00:00", by decide⟩ }] ∧
      (do
        let view ←
          executionView? (.minute (.constant "05") (.constant "02"))
            oldSource
        let applied ← view.applyTo (destinationWith .absent) |>.toOption
        pure (applied 1)) =
          some (.presentValue ⟨"05:02:00", by decide⟩) := by
  native_decide

/- Constant legality is position-specific and uses the pinned Java decimal-digit profile without imposing a width. -/
example :
    (operation? (.hour (.constant "23"))).isSome = true ∧
      (operation? (.hour (.constant "٢٣"))).isSome = true ∧
      operationError? (.hour (.constant "24")) =
        some (.components (.constantNotAdmitted .hour "24")) ∧
      operationError? (.minute (.constant "0") (.constant "60")) =
        some (.components (.constantNotAdmitted .minute "60")) ∧
      operationError? (.hour (.constant "2.0")) =
        some (.components (.constantNotAdmitted .hour "2.0")) := by
  native_decide

/- The operation samples the supplied world per call; equal structure with another world can produce another exact clock. -/
example :
    (do
      let operation ← worldLiteralOperation?
      let first ← worldOutcome? operation { now := { epochMillis := 18000000 } }
        oldSource
      let second ← worldOutcome? operation { now := { epochMillis := 21600000 } }
        oldSource
      pure (first, second)) =
        some (.accepted ⟨"05:00:00", by decide⟩,
          .accepted ⟨"06:00:00", by decide⟩) := by
  native_decide

/- An empty amount keeps the enclosing Time incomplete, while a reached formal amount remains exact poison. -/
example :
    (do
      let operation ← worldFieldOperation?
      let empty ← worldOutcome? operation
        { now := { epochMillis := 18000000 } } oldSource
      let formal ← worldOutcome? operation
        { now := { epochMillis := 18000000 } }
        (executionSource [
          componentCell 2 "bad" (.rejected .malformed)])
      pure (empty, formal)) =
        some (.noValue, .poison .malformed) := by
  native_decide

/- Static components inside the world carrier retain the same target-reference prohibition. -/
example :
    worldSelfReferenceError? = some (.targetSelfReference 1) := by
  native_decide

/- A dynamic accepted clock reaches the settled source-relative result and exact application path. -/
example :
    (do
      let operation ← worldLiteralOperation?
      let view ← worldView? operation
        { now := { epochMillis := 21600000 } } oldSource
      let applied ← view.applyTo (destinationWith .absent) |>.toOption
      pure (view.withChanges, applied 1)) =
        some ([{ targetField := 1, value := ⟨"06:00:00", by decide⟩ }],
          .presentValue ⟨"06:00:00", by decide⟩) := by
  native_decide

end A12Kernel.Conformance.TimeComputation
