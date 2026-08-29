import A12Kernel.Elaboration.DateTimeComputationApplication
import A12Kernel.Elaboration.DateTimeFirstFilledComputation

/-! # Direct one-star DateTime `FirstFilledValue` computation locks -/

namespace A12Kernel.Conformance.DateTimeFirstFilledComputation

open A12Kernel

private def dateTimeField (id : FieldId) (groups : GroupPath) (name : String)
    (scope : List RepeatableLevel := [])
    (format : String := "yyyy-MM-dd'T'HH:mm:ss")
    (components : TemporalComponents := TemporalComponents.now)
    (partialMode : TemporalPartialMode := .full) : FlatFieldDecl := {
  id
  groupPath := groups
  name
  policy := { kind := .temporal .dateTime components }
  temporalTargetPolicy := some { format, partialMode }
  repeatableScope := scope
}

private def target := dateTimeField 1 ["Cart"] "FirstMoment"
private def source := dateTimeField 2 ["Cart", "Lines"] "Moment" [10]
/- The different-**format** control uses the legal degenerate time-only format. The dotted
`dd.MM.yyyy'T'HH:mm:ss` spelling these controls used before is a DSL expression tag, not a declaration
format, and is refused outright. The format gate is kind-independent, so a DateTime field declaring
the clock format is authorable, and these two differ from the source in the format string alone. -/
private def degenerateSource := dateTimeField 3 ["Cart", "Lines"] "Dotted" [10] "HH:mm:ss"
private def incompleteSource := dateTimeField 4 ["Cart", "Lines"] "Incomplete" [10] "yyyy-MM-dd'T'HH:mm:ss" { TemporalComponents.now with second := false }
private def timeSource : FlatFieldDecl := {
  dateTimeField 5 ["Cart", "Lines"] "Time" [10] with
    policy := { kind := .temporal .time TemporalComponents.time }
    temporalTargetPolicy := some { format := "HH:mm:ss" }
}
private def repeatedTarget := dateTimeField 6 ["Cart", "Lines"] "RepeatedTarget" [10]
private def nestedSource := dateTimeField 7 ["Cart", "Lines", "Details"] "Nested" [10, 20]
private def degenerateTarget := dateTimeField 8 ["Cart"] "DottedTarget" [] "HH:mm:ss"
private def otherGroupTarget := dateTimeField 9 ["Other"] "OtherMoment"
private def partialSource := dateTimeField 11 ["Cart", "Lines"] "Partial" [10] "yyyy-MM-dd'T'HH:mm:ss" TemporalComponents.now .yearOptional

private def model : FlatModel := {
  fields := [target, source, degenerateSource, incompleteSource, timeSource, repeatedTarget, nestedSource, degenerateTarget, otherGroupTarget]
  repeatableGroups := [
    { level := 10, path := ["Cart", "Lines"], repeatability := some 99 },
    { level := 20, path := ["Cart", "Lines", "Details"], repeatability := some 4 }]
  timeZoneId := "UTC"
}

private def star (field : String) : SurfaceStarFieldPath := {
  base := .absolute
  groups := [{ name := "Cart" }, { name := "Lines", starred := true }]
  field
}

private def nestedStar : SurfaceStarFieldPath := {
  base := .absolute
  groups := [{ name := "Cart" }, { name := "Lines", starred := true }, { name := "Details", starred := true }]
  field := "Nested"
}

private def checkedAt? (declaringGroup : GroupPath) (targetField : FieldId) (authored : SurfaceStarFieldPath) :=
  (checkDateTimeFirstFilledComputation model declaringGroup targetField authored).toOption

private def checked? (targetField : FieldId) (authored : SurfaceStarFieldPath) :=
  checkedAt? ["Cart"] targetField authored

private def prepared : PreparedFlatStringContext model builtinStringPatternCompiler :=
  (prepareFlatStringContext { now := { epochMillis := 0 } } builtinStringPatternCompiler model).toOption.get (by native_decide)

private def clock (hour minute second : Nat) (valid : hour < 24 ∧ minute < 60 ∧ second < 60) : TimeOfDay :=
  ⟨hour, minute, second, valid⟩

private def dateTimeValue (millis : Int) (parts : DateParts) (time : TimeOfDay) : Value :=
  .temporal (.dateTime { epochMillis := millis } parts time .storedGregorian)

private structure SourceInput where
  row : Nat
  stored : String
  raw : RawCell

private def selectedInput (row : Nat) : SourceInput := {
  row
  stored := "2024-03-20T10:11:12"
  raw := .parsed (dateTimeValue 1710929472000 { year := 2024, month := 3, day := 20 } (clock 10 11 12 (by decide)))
}

private def malformedInput (row : Nat) : SourceInput :=
  { row, stored := "XX", raw := .rejected .malformed }

private def checkedDocument? (cells : List ClassifiedCellInput) :
    Option (CheckedDocument model) :=
  (checkDocument prepared "en_US" {
    instantiatedRows := [{ group := 10, path := [1] }, { group := 10, path := [2] }]
    cells
  }).toOption

private def inputWithTarget? (targetStored : String) (targetRaw : RawCell)
    (sourceInputs : List SourceInput) : Option (CheckedDocument model) :=
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

private def input? (sourceInputs : List SourceInput) : Option (CheckedDocument model) :=
  inputWithTarget? "2000-01-01T12:34:56"
    (.parsed (dateTimeValue 946730096000
      { year := 2000, month := 1, day := 1 }
      (clock 12 34 56 (by decide)))) sourceInputs

private def outcome? (sourceInputs : List SourceInput) : Option DateTimeTargetOutcome := do
  let operation ← checked? target.id (star "Moment")
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
    Option (DateTimeComputationRunView FormalCause) := do
  let operation ← checked? target.id (star "Moment")
  let input ← inputWithTarget? targetStored targetRaw sourceInputs
  operation.executeResult input residualMessages |>.toOption

private def selectedValue : StoredDateTime :=
  ⟨"2024-03-20T10:11:12", by decide⟩
private def seedValue : StoredDateTime :=
  ⟨"2000-01-01T12:34:56", by decide⟩
private def otherValue : StoredDateTime :=
  ⟨"2024-04-01T06:00:00", by decide⟩

private def otherCell : ClassifiedCellInput := {
  address := { field := otherGroupTarget.id, path := [] }
  stored := otherValue.text
  raw := .parsed (dateTimeValue 1711951200000
    { year := 2024, month := 4, day := 1 }
    (clock 6 0 0 (by decide)))
}

private def destinationFor? (includeTarget : Bool) :
    Option (CheckedDocument model) :=
  let targetCells := if includeTarget then [{
    address := { field := target.id, path := [] }
    stored := seedValue.text
    raw := .parsed (dateTimeValue 946730096000
      { year := 2000, month := 1, day := 1 }
      (clock 12 34 56 (by decide)))
  }] else []
  checkedDocument? (targetCells ++ [otherCell])

/- The retained temporal-family probe calibrates CLEARED, a filled VALUE, and leading-empty continuation for this carrier using a different filled literal; the exact `2024-03-20T10:11:12` bytes here remain internal. -/
example :
    signature? [] = some "CLEARED" ∧
      signature? [selectedInput 1] = some "VALUE|2024-03-20T10:11:12" ∧
      signature? [selectedInput 2] = some "VALUE|2024-03-20T10:11:12" := by
  native_decide

/- The checked FirstFilled operation classifies and applies its model-zone-rendered instant through the established DateTime result path while preserving unrelated destination state. -/
example : (do
    let view ← runView? seedValue.text
      (.parsed (dateTimeValue 946730096000
        { year := 2000, month := 1, day := 1 }
        (clock 12 34 56 (by decide)))) [selectedInput 1]
    let destination ← destinationFor? true
    let applied ← view.applyToChecked destination |>.toOption
    pure (view.withoutErrors, view.withChanges,
      applied target.id, applied otherGroupTarget.id)) =
    some ([{ targetField := target.id, value := selectedValue }],
      [{ targetField := target.id, value := selectedValue }],
      .presentValue selectedValue, .presentValue otherValue) := by
  native_decide

/- Change classification remains source-relative: a result equal to the source target is public but inert against a different destination target. -/
example : (do
    let view ← runView? selectedValue.text
      (.parsed (dateTimeValue 1710929472000
        { year := 2024, month := 3, day := 20 }
        (clock 10 11 12 (by decide)))) [selectedInput 1]
    let destination ← destinationFor? true
    let applied ← view.applyToChecked destination |>.toOption
    pure (view.withoutErrors, view.withChanges, applied target.id)) =
    some ([{ targetField := target.id, value := selectedValue }], [],
      .presentValue seedValue) := by
  native_decide

/- Exhaustion and a reached formal cause both retain a source-filled clear and materialize an absent destination target without disturbing unrelated state. -/
example :
    (do
      let view ← runView? seedValue.text
        (.parsed (dateTimeValue 946730096000
          { year := 2000, month := 1, day := 1 }
          (clock 12 34 56 (by decide)))) []
      let destination ← destinationFor? false
      let applied ← view.applyToChecked destination |>.toOption
      pure (view.cleared, view.noErrorOccurred,
        applied target.id, applied otherGroupTarget.id)) =
      some ([target.id], true, .presentEmpty, .presentValue otherValue) ∧
    (do
      let view ← runView? seedValue.text
        (.parsed (dateTimeValue 946730096000
          { year := 2000, month := 1, day := 1 }
          (clock 12 34 56 (by decide)))) [malformedInput 1]
      let destination ← destinationFor? false
      let applied ← view.applyToChecked destination |>.toOption
      pure (view.cleared, view.noErrorOccurred,
        applied target.id, applied otherGroupTarget.id)) =
      some ([target.id], true, .presentEmpty, .presentValue otherValue) := by
  native_decide

/- The typed adapter retains the exact instant rather than source text or a supplied wall label; this mechanism separator is internal. -/
example :
    signature? [{
      row := 1
      stored := "2001-02-03T04:05:06"
      raw := .parsed (dateTimeValue 1710929472000 { year := 2001, month := 2, day := 3 } (clock 4 5 6 (by decide)))
    }] = some "VALUE|2024-03-20T10:11:12" := by
  native_decide

/- First-present and first-formal terminals both hide the suffix. -/
example :
    signature? [selectedInput 1, malformedInput 2] = some "VALUE|2024-03-20T10:11:12" ∧
      signature? [malformedInput 1, selectedInput 2] = some "POISON" := by
  native_decide

/- Admission is limited to one complete ISO DateTime carrier and one direct single-level star. Placement is unconstrained. Declaring at the source's own repeatable group puts the fixed target *above* the declaring group, which the checkpoint's `star-rowgroup` row measures as admitted: a star aggregate derives no iteration, so the Kernel's containment gate cannot fire. An unrepresentable declaring group is still refused. Varying the declaring group rather than the target's group keeps the fixture to one model root, as an authored A12 model is. -/
example :
    (checked? target.id (star "Moment")).isSome = true ∧
      (checked? target.id (star "Dotted")).isNone = true ∧
      (checked? target.id (star "Incomplete")).isNone = true ∧
      (checked? target.id (star "Time")).isNone = true ∧
      partialSource.temporalFirstFilledStarCarrier? = none ∧
      (checked? degenerateTarget.id (star "Moment")).isNone = true ∧
      (checkedAt? ["Cart", "Lines"] target.id (star "Moment")).isSome = true ∧
      (checkedAt? [] target.id (star "Moment")).isNone = true ∧
      (checkedAt? ["Cart", "Lines"] repeatedTarget.id (star "Moment")).isNone = true ∧
      (checked? target.id nestedStar).isNone = true := by
  native_decide

end A12Kernel.Conformance.DateTimeFirstFilledComputation
