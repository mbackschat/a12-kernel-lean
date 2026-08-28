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

private def other : FlatFieldDecl := {
  target with id := 5, name := "OtherTime"
}

private def stringTarget : FlatFieldDecl := {
  id := 6
  groupPath := ["Order"]
  name := "Label"
  policy := { kind := .string }
}

private def repeatedTarget : FlatFieldDecl := {
  target with
  id := 7
  groupPath := ["Order", "Lines"]
  name := "RepeatedTime"
  repeatableScope := [10]
}

private def incompleteTarget : FlatFieldDecl := {
  target with
  id := 8
  name := "MinuteTime"
  policy := { kind := .temporal .time {
    TemporalComponents.time with second := false
  } }
}

private def repeatedStringTarget : FlatFieldDecl := {
  stringTarget with
  id := 9
  groupPath := ["Order", "Lines"]
  name := "RepeatedLabel"
  repeatableScope := [10]
}

private def applicationModel : FlatModel := {
  fields := [target, other]
  timeZoneId := "UTC"
}

private def validationModel : FlatModel := {
  fields := [stringTarget, repeatedTarget, incompleteTarget,
    repeatedStringTarget]
  repeatableGroups := [{
    level := 10
    path := ["Order", "Lines"]
    repeatability := some 3
  }]
  timeZoneId := "UTC"
}

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

private def otherTime : StoredTime := ⟨"06:00:00", by decide⟩

private def sourceAt (field : FieldId) (stored : String)
    (raw : RawCell) : DocumentData := {
  instantiatedRows := []
  cells := [{ address := { field, path := [] }, stored, raw }] }

private def source (stored : String) (raw : RawCell) : DocumentData :=
  sourceAt 1 stored raw

private def oldSource : DocumentData :=
  source oldTime.text (.parsed (.temporal
    (.time { epochMillis := 0 } (clock 5 2 8 (by decide)))))

private def prepared :=
  (prepareFlatStringContext { now := { epochMillis := 0 } }
    builtinStringPatternCompiler (model)).toOption.get (by native_decide)

private def applicationPrepared :=
  (prepareFlatStringContext { now := { epochMillis := 0 } }
    builtinStringPatternCompiler applicationModel).toOption.get
      (by native_decide)

private def constructionView? (input : DocumentData)
    (outcome : TimeTargetOutcome)
    (messages : List FormalCause := []) :
    Option (TimeComputationRunView FormalCause) := do
  let checked ← (checkDocument prepared "en_US" input).toOption
  pure (TimeComputationRunView.fromOutcomes checked messages
    [(1, outcome)])

private def checkedApplication? (input : DocumentData) :
    Option (CheckedDocument applicationModel) :=
  (checkDocument applicationPrepared "en_US" input).toOption

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

/- Typed Time ingress classifies construction results by ordinary stored-clock equality. -/
example :
    (constructionView? oldSource (.accepted oldTime)).map
        (fun view => (view.withoutErrors, view.withChanges)) =
      some ([{ targetField := 1, value := oldTime }],
        []) ∧
    (constructionView? oldSource (.accepted nextTime)).map
        (fun view => (view.withoutErrors, view.withChanges)) =
      some ([{ targetField := 1, value := nextTime }],
        [{ targetField := 1, value := nextTime }]) := by
  native_decide

/- Quiet no-value and poison clear only a source-filled target and manufacture no target-local error. -/
example :
    (constructionView? oldSource .noValue).map
        (fun view => (view.cleared, view.withErrors)) = some ([1], []) ∧
      (constructionView? { instantiatedRows := [], cells := [] }
        .noValue).map
        (·.cleared) = some [] ∧
      (constructionView? (source "" .presentEmpty) .noValue).map
        (·.cleared) = some [] ∧
      (constructionView? oldSource (.poison .malformed)).map
        (fun view => (view.cleared, view.noErrorOccurred)) =
          some ([1], true) := by
  native_decide

/- Application writes changed text, applies a retained clear to filled or absent destinations, and ignores residual messages. -/
example :
    (do
      let view ← constructionView? oldSource (.accepted nextTime) [.malformed]
      let applied ← view.applyTo (destinationWith .absent) |>.toOption
      pure (applied 1, view.noErrorOccurred)) =
        some (.presentValue nextTime, false) ∧
      (do
        let view ← constructionView? oldSource .noValue
        let applied ← view.applyTo
          (destinationWith (.presentValue nextTime)) |>.toOption
        pure (applied 1)) = some .presentEmpty ∧
      (do
        let view ← constructionView? oldSource .noValue
        let applied ← view.applyTo (destinationWith .absent) |>.toOption
        pure (applied 1)) = some .presentEmpty := by
  native_decide

/- A source-identical typed Time construction produces no action and preserves a different destination clock. -/
example :
    (do
      let view ← constructionView? oldSource (.accepted oldTime)
      let applied ←
        view.applyTo (destinationWith (.presentValue nextTime)) |>.toOption
      pure (view.withChanges, applied 1)) =
      some ([], .presentValue nextTime) := by
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

/- Checked application preserves the separate destination and unrelated value when typed source identity suppresses the action. -/
example : (do
    let view ← constructionView? oldSource (.accepted oldTime)
    let checked ← checkedApplication? {
      instantiatedRows := []
      cells := (source nextTime.text (.parsed (.temporal
        (.time { epochMillis := 0 } (clock 5 2 9 (by decide)))))).cells ++
        (sourceAt other.id otherTime.text
        (.parsed (.temporal
          (.time { epochMillis := 3600000 }
            (clock 6 0 0 (by decide)))))).cells
    }
    let applied ← view.applyToChecked checked |>.toOption
    pure (applied target.id, applied other.id)) =
      some (.presentValue nextTime, .presentValue otherTime) := by
  native_decide

/- Checked target validation retains the exact lookup cause and separates family and scope failures. -/
example :
    (match TimeComputationRunView.validateActionTargets
        validationModel [99] with
      | .error (.targetField 99 (.unknownFieldId 99)) => true
      | _ => false) = true ∧
    (match TimeComputationRunView.validateActionTargets
        validationModel [stringTarget.id] with
      | .error (.nonTimeTarget field) => field == stringTarget.id
      | _ => false) = true ∧
    (match TimeComputationRunView.validateActionTargets
        validationModel [repeatedTarget.id] with
      | .error (.repeatableTarget field) => field == repeatedTarget.id
      | _ => false) = true := by
  native_decide

/- Time requires the complete whole-second component set. -/
example : (match TimeComputationRunView.validateActionTargets
    validationModel [incompleteTarget.id] with
  | .error (.nonTimeTarget field) => field == incompleteTarget.id
  | _ => false) = true := by
  native_decide

/- Family rejection precedes repeatable-scope rejection. -/
example : (match TimeComputationRunView.validateActionTargets
    validationModel [repeatedStringTarget.id] with
  | .error (.nonTimeTarget field) => field == repeatedStringTarget.id
  | _ => false) = true := by
  native_decide

/- Duplicate actions fail before checked target validation. -/
example : (do
    let sourceChecked ←
      (checkDocument prepared "en_US"
        { instantiatedRows := [], cells := [] }).toOption
    let destinationChecked ← checkedApplication?
      { instantiatedRows := [], cells := [] }
    let view := TimeComputationRunView.fromOutcomes sourceChecked
      ([] : List FormalCause)
      [(99, .accepted nextTime), (99, .accepted oldTime)]
    pure (match view.applyToChecked destinationChecked with
      | .error (.duplicateActionTarget field) => field == 99
      | _ => false)) = some true := by
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

/- Checked nonrepeatable `Time(...)` execution applies ordinary typed source equality. -/
example :
    (executionView? (.second
      (.constant "05") (.constant "02") (.constant "08"))
      oldSource).map (fun view => (view.withoutErrors, view.withChanges)) =
      some ([{ targetField := 1, value := oldTime }],
        []) := by
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

/- Scalar and repeatable world-aware plans share the authored dependency projection. -/
example :
    worldLiteralOperation?.map (·.fieldDependencies) = some [] ∧
      worldFieldOperation?.map (·.fieldDependencies) = some [2] := by
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

/- World-aware nonrepeatable `Time(...)` execution applies the same typed source equality. -/
example :
    (do
      let operation ← worldLiteralOperation?
      let sourceClock := clock 5 0 0 (by decide)
      let sourceInput := source "05:00:00" (.parsed (.temporal
        (.time { epochMillis := 18000000 } sourceClock)))
      let view ← worldView? operation
        { now := { epochMillis := 18000000 } } sourceInput
      pure view.withChanges) =
      some [] := by
  native_decide

private def addressedConstructionModel : FlatModel := {
  fields := [repeatedTarget, other]
  repeatableGroups := [{
    level := 10
    path := ["Order", "Lines"]
    repeatability := some 3
  }] }

private def addressedConstructionPrepared :
    PreparedFlatStringContext addressedConstructionModel
      builtinStringPatternCompiler :=
  (prepareFlatStringContext { now := { epochMillis := 0 } }
    builtinStringPatternCompiler addressedConstructionModel).toOption.get
      (by native_decide)

private def addressedConstructionOperation? :=
  (checkAddressedTimeConstantConstructionComputation
    addressedConstructionModel ["Order", "Lines"] repeatedTarget.id
    (.second "5" "2" "9")).toOption

private def addressedConstructionOutcome?
    (components : SurfaceAddressedTimeConstantComponents) :
    Option TimeTargetOutcome := do
  let operation ← (checkAddressedTimeConstantConstructionComputation
    addressedConstructionModel ["Order", "Lines"] repeatedTarget.id
    components).toOption
  let input ← (checkDocument addressedConstructionPrepared "en_US" {
    instantiatedRows := [{ group := 10, path := [1] }]
    cells := []
  }).toOption
  let outcomes ← operation.execute input |>.toOption
  outcomes.head?.map AddressedTimeConstructionOutcome.outcome

/- The addressed checker retains the canonical zero-through-three constant prefix and separates all three position gates. -/
example :
    addressedConstructionOutcome? .empty =
      some (.accepted ⟨"00:00:00", by decide⟩) ∧
    addressedConstructionOutcome? (.hour "10") =
      some (.accepted ⟨"10:00:00", by decide⟩) ∧
    addressedConstructionOutcome? (.minute "5" "24") =
      some (.accepted ⟨"05:24:00", by decide⟩) ∧
    addressedConstructionOutcome? (.second "5" "2" "24") =
      some (.accepted ⟨"05:02:24", by decide⟩) ∧
    (match checkAddressedTimeConstantConstructionComputation
        addressedConstructionModel ["Order", "Lines"] repeatedTarget.id
        (.hour "24") with
      | .error (.component (.constantNotAdmitted .hour "24")) => true
      | _ => false) = true ∧
    (match checkAddressedTimeConstantConstructionComputation
        addressedConstructionModel ["Order", "Lines"] repeatedTarget.id
        (.minute "5" "60") with
      | .error (.component (.constantNotAdmitted .minute "60")) => true
      | _ => false) = true ∧
    (match checkAddressedTimeConstantConstructionComputation
        addressedConstructionModel ["Order", "Lines"] repeatedTarget.id
        (.second "5" "2" "60") with
      | .error (.component (.constantNotAdmitted .second "60")) => true
      | _ => false) = true := by
  native_decide

private def addressedConstructionDocument?
    (rows : List RowAddr) (cells : List ClassifiedCellInput) :=
  (checkDocument addressedConstructionPrepared "en_US"
    { instantiatedRows := rows, cells }).toOption

private def addressedConstructionInput? :=
  addressedConstructionDocument? [
    { group := 10, path := [1] }, { group := 10, path := [2] },
    { group := 10, path := [3] }] [
    { address := { field := repeatedTarget.id, path := [1] }
      stored := nextTime.text
      raw := .parsed (.temporal (.time { epochMillis := 0 }
        (clock 5 2 9 (by decide)))) },
    { address := { field := repeatedTarget.id, path := [2] }
      stored := oldTime.text
      raw := .parsed (.temporal (.time { epochMillis := 0 }
        (clock 5 2 8 (by decide)))) },
    { address := { field := other.id, path := [] }
      stored := otherTime.text
      raw := .parsed (.temporal (.time { epochMillis := 0 }
        (clock 6 0 0 (by decide)))) }]

/- Repeatable construction keeps every exact success but uses ordinary row-local source equality for the change projection and separate-destination application. -/
example : (do
    let operation ← addressedConstructionOperation?
    let input ← addressedConstructionInput?
    let result ← operation.executeResult input ([] : List FormalCause)
      |>.toOption
    let destination ← addressedConstructionDocument? [
      { group := 10, path := [1] }, { group := 10, path := [2] },
      { group := 10, path := [3] }] []
    let applied ← result.applyToChecked destination |>.toOption
    pure (
      result.time.withoutErrors.map (fun item => item.targetField),
      result.time.withChanges.map (fun item => item.targetField),
      applied { field := repeatedTarget.id, path := [1] },
      applied { field := repeatedTarget.id, path := [2] },
      applied { field := repeatedTarget.id, path := [3] })) = some (
        [{ field := repeatedTarget.id, path := [1] },
          { field := repeatedTarget.id, path := [2] },
          { field := repeatedTarget.id, path := [3] }],
        [{ field := repeatedTarget.id, path := [2] },
          { field := repeatedTarget.id, path := [3] }],
        .absent, .presentValue nextTime, .presentValue nextTime) := by
  native_decide

/- With no physical target row, the addressed constructor produces no result or action. -/
example : (do
    let operation ← addressedConstructionOperation?
    let input ← addressedConstructionDocument? [] []
    operation.execute input |>.toOption) = some [] := by
  native_decide

private def nestedAddressedConstructionTarget : FlatFieldDecl := {
  repeatedTarget with
  id := 10
  groupPath := ["Order", "Projects", "Tasks"]
  repeatableScope := [10, 20]
}

private def nestedAddressedConstructionModel : FlatModel := {
  fields := [nestedAddressedConstructionTarget]
  repeatableGroups := [
    { level := 10, path := ["Order", "Projects"], repeatability := some 3 },
    { level := 20, path := ["Order", "Projects", "Tasks"],
      repeatability := some 3 }
  ]
}

private def nestedAddressedConstructionPrepared :
    PreparedFlatStringContext nestedAddressedConstructionModel
      builtinStringPatternCompiler :=
  (prepareFlatStringContext { now := { epochMillis := 0 } }
    builtinStringPatternCompiler nestedAddressedConstructionModel).toOption.get
      (by native_decide)

/- Physical target rows retain their complete nested coordinates and encounter order rather than sorting or truncating paths. -/
example : (do
    let operation ← (checkAddressedTimeConstantConstructionComputation
      nestedAddressedConstructionModel ["Order", "Projects", "Tasks"]
      nestedAddressedConstructionTarget.id (.hour "5")).toOption
    let input ← (checkDocument nestedAddressedConstructionPrepared "en_US" {
      instantiatedRows := [
        { group := 10, path := [1] },
        { group := 20, path := [1, 3] }, { group := 20, path := [1, 1] },
        { group := 20, path := [1, 2] }]
      cells := []
    }).toOption
    let outcomes ← operation.execute input |>.toOption
    pure (outcomes.map (fun entry => entry.targetField))) = some [
      { field := nestedAddressedConstructionTarget.id, path := [1, 3] },
      { field := nestedAddressedConstructionTarget.id, path := [1, 1] },
      { field := nestedAddressedConstructionTarget.id, path := [1, 2] }
    ] := by
  native_decide

end A12Kernel.Conformance.TimeComputation
