import A12Kernel.Elaboration.TimeFirstFilledComputation

/-! # Direct one-star Time `FirstFilledValue` computation locks -/

namespace A12Kernel.Conformance.TimeFirstFilledComputation

open A12Kernel

private def timeField (id : FieldId) (groups : GroupPath) (name : String)
    (scope : List RepeatableLevel := [])
    (format : String := "HH:mm:ss")
    (components : TemporalComponents := TemporalComponents.time)
    (partialMode : TemporalPartialMode := .full)
    (youngerThan1900Check : Bool := false) : FlatFieldDecl := {
  id
  groupPath := groups
  name
  policy := { kind := .temporal .time components }
  temporalTargetPolicy := some {
    format
    partialMode
    youngerThan1900Check
  }
  repeatableScope := scope
}

private def target := timeField 1 ["Cart"] "FirstTime"
private def source := timeField 2 ["Cart", "Lines"] "Time" [10]
private def shortSource :=
  timeField 3 ["Cart", "Lines"] "ShortTime" [10] "HH:mm"
private def incompleteSource :=
  timeField 4 ["Cart", "Lines"] "IncompleteTime" [10] "HH:mm:ss" {
    year := false
    month := false
    day := false
    hour := true
    minute := true
    second := false
  }
private def dateSource : FlatFieldDecl := {
  id := 5
  groupPath := ["Cart", "Lines"]
  name := "Date"
  policy := { kind := .temporal .date TemporalComponents.fullDate }
  temporalTargetPolicy := some { format := "HH:mm:ss" }
  repeatableScope := [10]
}
private def repeatedTarget :=
  timeField 6 ["Cart", "Lines"] "RepeatedTarget" [10]
private def nestedSource :=
  timeField 7 ["Cart", "Lines", "Details"] "NestedTime" [10, 20]
private def otherFormatTarget :=
  timeField 8 ["Cart"] "ShortTarget" [] "HH:mm"
private def otherGroupTarget := timeField 9 ["Other"] "OtherTime"
private def partialSource :=
  timeField 11 ["Cart", "Lines"] "PartialTime" [10] "HH:mm:ss"
    TemporalComponents.time .yearOptional
private def checkedSource :=
  timeField 12 ["Cart", "Lines"] "CheckedTime" [10] "HH:mm:ss"
    TemporalComponents.time .full true

private def model : FlatModel := {
  fields := [
    target, source, shortSource, incompleteSource, dateSource,
    repeatedTarget, nestedSource, otherFormatTarget, otherGroupTarget]
  repeatableGroups := [
    { level := 10, path := ["Cart", "Lines"], repeatability := some 99 },
    { level := 20, path := ["Cart", "Lines", "Details"],
      repeatability := some 4 }]
}

private def star (field : String) : SurfaceStarFieldPath := {
  base := .absolute
  groups := [{ name := "Cart" }, { name := "Lines", starred := true }]
  field
}

private def nestedStar : SurfaceStarFieldPath := {
  base := .absolute
  groups := [
    { name := "Cart" },
    { name := "Lines", starred := true },
    { name := "Details", starred := true }]
  field := "NestedTime"
}

private def checkedAt? (declaringGroup : GroupPath) (targetField : FieldId)
    (authored : SurfaceStarFieldPath) :=
  (checkTimeFirstFilledComputation
    model declaringGroup targetField authored).toOption

private def checked? (targetField : FieldId) (authored : SurfaceStarFieldPath) :=
  checkedAt? ["Cart"] targetField authored

private def prepared :
    PreparedFlatStringContext model builtinStringPatternCompiler :=
  (prepareFlatStringContext { now := { epochMillis := 0 } }
    builtinStringPatternCompiler model).toOption.get (by native_decide)

private def clock (hour minute second : Nat)
    (valid : hour < 24 ∧ minute < 60 ∧ second < 60) : TimeOfDay :=
  ⟨hour, minute, second, valid⟩

private def selectedClock := clock 10 11 12 (by decide)
private def seedClock := clock 12 34 56 (by decide)

private def timeValue (epochMillis : Int) (value : TimeOfDay) : Value :=
  .temporal (.time { epochMillis } value)

private structure SourceInput where
  row : Nat
  stored : String
  raw : RawCell

private def selectedInput (row : Nat) (stored : String := "10:11:12")
    (epochMillis : Int := 36672000) : SourceInput := {
  row
  stored
  raw := .parsed (timeValue epochMillis selectedClock)
}

private def malformedInput (row : Nat) : SourceInput :=
  { row, stored := "XX", raw := .rejected .malformed }

private def checkedDocument? (cells : List ClassifiedCellInput) :
    Option (CheckedDocument model) :=
  (checkDocument prepared "en_US" {
    instantiatedRows := [
      { group := 10, path := [1] },
      { group := 10, path := [2] }]
    cells
  }).toOption

private def inputWithTarget? (targetStored : String) (targetRaw : RawCell)
    (sourceInputs : List SourceInput) :
    Option (CheckedDocument model) :=
  let sourceCells := sourceInputs.map fun input => {
    address := { field := source.id, path := [input.row] }
    stored := input.stored
    raw := input.raw
  }
  checkedDocument? ([{
    address := { field := target.id, path := [] }
    stored := targetStored
    raw := targetRaw
  }] ++ sourceCells)

private def input? (sourceInputs : List SourceInput) :
    Option (CheckedDocument model) :=
  inputWithTarget? "12:34:56"
    (.parsed (timeValue 45296000 seedClock)) sourceInputs

private def outcome? (sourceInputs : List SourceInput) :
    Option TimeTargetOutcome := do
  let operation ← checked? target.id (star "Time")
  let input ← input? sourceInputs
  operation.execute input |>.toOption

private def signature? (sourceInputs : List SourceInput) : Option String := do
  let outcome ← outcome? sourceInputs
  pure (match outcome with
    | .noValue => "CLEARED"
    | .accepted stored => "VALUE|" ++ stored.text
    | .poison _ => "POISON")

private def runView? (targetStored : String) (targetRaw : RawCell)
    (sourceInputs : List SourceInput)
    (residualMessages : List FormalCause := []) :
    Option (TimeComputationRunView FormalCause) := do
  let operation ← checked? target.id (star "Time")
  let input ← inputWithTarget? targetStored targetRaw sourceInputs
  operation.executeResult input residualMessages |>.toOption

private def selectedTime : StoredTime := ⟨"10:11:12", by decide⟩
private def seedTime : StoredTime := ⟨"12:34:56", by decide⟩
private def otherTime : StoredTime := ⟨"06:00:00", by decide⟩

private def otherCell : ClassifiedCellInput := {
  address := { field := otherGroupTarget.id, path := [] }
  stored := otherTime.text
  raw := .parsed (timeValue 21600000 (clock 6 0 0 (by decide)))
}

private def destinationFor? (includeTarget : Bool) :
    Option (CheckedDocument model) :=
  let targetCells := if includeTarget then [{
    address := { field := target.id, path := [] }
    stored := seedTime.text
    raw := .parsed (timeValue 45296000 seedClock)
  }] else []
  checkedDocument? (targetCells ++ [otherCell])

/- The retained temporal-family probe calibrates CLEARED, a filled VALUE, and leading-empty continuation for this carrier using a different filled literal; the exact `10:11:12` bytes here remain internal. -/
example :
    signature? [] = some "CLEARED" ∧
      signature? [selectedInput 1] = some "VALUE|10:11:12" ∧
      signature? [selectedInput 2] = some "VALUE|10:11:12" := by
  native_decide

/- The checked FirstFilled operation classifies and applies its rendered clock through the established Time result path while preserving unrelated destination state. -/
example : (do
    let view ← runView? seedTime.text
      (.parsed (timeValue 45296000 seedClock)) [selectedInput 1]
    let destination ← destinationFor? true
    let applied ← view.applyToChecked destination |>.toOption
    pure (view.withoutErrors, view.withChanges,
      applied target.id, applied otherGroupTarget.id)) =
    some ([{ targetField := target.id, value := selectedTime }],
      [{ targetField := target.id, value := selectedTime }],
      .presentValue selectedTime, .presentValue otherTime) := by
  native_decide

/- A source-identical selected clock produces no changed action and therefore preserves a different destination target. -/
example : (do
    let view ← runView? selectedTime.text
      (.parsed (timeValue 36672000 selectedClock)) [selectedInput 1]
    let destination ← destinationFor? true
    let applied ← view.applyToChecked destination |>.toOption
    pure (view.withChanges, applied target.id)) =
    some ([], .presentValue seedTime) := by
  native_decide

/- Exhaustion and a reached formal cause both retain a source-filled clear and materialize an absent destination target without disturbing unrelated state. -/
example :
    (do
      let view ← runView? seedTime.text
        (.parsed (timeValue 45296000 seedClock)) []
      let destination ← destinationFor? false
      let applied ← view.applyToChecked destination |>.toOption
      pure (view.cleared, view.noErrorOccurred,
        applied target.id, applied otherGroupTarget.id)) =
      some ([target.id], true, .presentEmpty, .presentValue otherTime) ∧
    (do
      let view ← runView? seedTime.text
        (.parsed (timeValue 45296000 seedClock)) [malformedInput 1]
      let destination ← destinationFor? false
      let applied ← view.applyToChecked destination |>.toOption
      pure (view.cleared, view.noErrorOccurred,
        applied target.id, applied otherGroupTarget.id)) =
      some ([target.id], true, .presentEmpty, .presentValue otherTime) := by
  native_decide

/- The typed adapter retains the parsed clock rather than the stored text or transport instant; this mechanism separator is internal. -/
example :
    signature? [selectedInput 1 "01:02:03" 0] =
      some "VALUE|10:11:12" := by
  native_decide

/- First-present and first-formal terminals both hide the suffix; these order branches remain externally uncalibrated. -/
example :
    signature? [selectedInput 1, malformedInput 2] =
        some "VALUE|10:11:12" ∧
      signature? [malformedInput 1, selectedInput 2] = some "POISON" := by
  native_decide

/- The checked boundary admits only the bounded fixed `HH:mm:ss` Time target and direct single-level starred source. Placement is unconstrained. Declaring at the source's own repeatable group puts the fixed target *above* the declaring group, which the checkpoint's `star-rowgroup` row measures as admitted: a star aggregate derives no iteration, so the Kernel's containment gate cannot fire. An unrepresentable declaring group is still refused. Varying the declaring group rather than the target's group keeps the fixture to one model root, as an authored A12 model is. -/
example :
    (checked? target.id (star "Time")).isSome = true ∧
      (checked? target.id (star "ShortTime")).isNone = true ∧
      (checked? target.id (star "IncompleteTime")).isNone = true ∧
      (checked? target.id (star "Date")).isNone = true ∧
      partialSource.temporalFirstFilledStarCarrier? = none ∧
      checkedSource.temporalFirstFilledStarCarrier? = none ∧
      (checked? otherFormatTarget.id (star "Time")).isNone = true ∧
      (checkedAt? ["Cart", "Lines"] target.id (star "Time")).isSome = true ∧
      (checkedAt? [] target.id (star "Time")).isNone = true ∧
      (checkedAt? ["Cart", "Lines"] repeatedTarget.id
        (star "Time")).isNone = true ∧
      (checked? target.id nestedStar).isNone = true := by
  native_decide

end A12Kernel.Conformance.TimeFirstFilledComputation
