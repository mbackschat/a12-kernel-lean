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
private def dottedSource := dateTimeField 3 ["Cart", "Lines"] "Dotted" [10] "dd.MM.yyyy'T'HH:mm:ss"
private def incompleteSource := dateTimeField 4 ["Cart", "Lines"] "Incomplete" [10] "yyyy-MM-dd'T'HH:mm:ss" { TemporalComponents.now with second := false }
private def timeSource : FlatFieldDecl := {
  dateTimeField 5 ["Cart", "Lines"] "Time" [10] with
    policy := { kind := .temporal .time TemporalComponents.time }
    temporalTargetPolicy := some { format := "HH:mm:ss" }
}
private def repeatedTarget := dateTimeField 6 ["Cart", "Lines"] "RepeatedTarget" [10]
private def nestedSource := dateTimeField 7 ["Cart", "Lines", "Details"] "Nested" [10, 20]
private def dottedTarget := dateTimeField 8 ["Cart"] "DottedTarget" [] "dd.MM.yyyy'T'HH:mm:ss"
private def otherGroupTarget := dateTimeField 9 ["Other"] "OtherMoment"
private def partialSource := dateTimeField 11 ["Cart", "Lines"] "Partial" [10] "yyyy-MM-dd'T'HH:mm:ss" TemporalComponents.now .yearOptional

private def model : FlatModel := {
  fields := [target, source, dottedSource, incompleteSource, timeSource, repeatedTarget, nestedSource, dottedTarget, otherGroupTarget]
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

private def input? (sourceInputs : List SourceInput) : Option (CheckedDocument model) :=
  let sourceCells := sourceInputs.map fun input => {
    address := { field := source.id, path := [input.row] }
    stored := input.stored
    raw := input.raw
  }
  (checkDocument prepared "en_US" {
    instantiatedRows := [{ group := 10, path := [1] }, { group := 10, path := [2] }]
    cells := [{
      address := { field := target.id, path := [] }
      stored := "2000-01-01T12:34:56"
      raw := .parsed (dateTimeValue 946730096000 { year := 2000, month := 1, day := 1 } (clock 12 34 56 (by decide)))
    }] ++ sourceCells
  }).toOption

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

/- The retained temporal-family probe calibrates CLEARED, a filled VALUE, and leading-empty continuation for this carrier using a different filled literal; the exact `2024-03-20T10:11:12` bytes here remain internal. -/
example :
    signature? [] = some "CLEARED" ∧
      signature? [selectedInput 1] = some "VALUE|2024-03-20T10:11:12" ∧
      signature? [selectedInput 2] = some "VALUE|2024-03-20T10:11:12" := by
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

/- Admission is limited to one complete ISO DateTime carrier and one direct single-level star. -/
example :
    (checked? target.id (star "Moment")).isSome = true ∧
      (checked? target.id (star "Dotted")).isNone = true ∧
      (checked? target.id (star "Incomplete")).isNone = true ∧
      (checked? target.id (star "Time")).isNone = true ∧
      partialSource.temporalFirstFilledStarCarrier? = none ∧
      (checked? dottedTarget.id (star "Moment")).isNone = true ∧
      (checked? otherGroupTarget.id (star "Moment")).isNone = true ∧
      (checkedAt? ["Cart", "Lines"] repeatedTarget.id (star "Moment")).isNone = true ∧
      (checked? target.id nestedStar).isNone = true := by
  native_decide

end A12Kernel.Conformance.DateTimeFirstFilledComputation
