import A12Kernel.Elaboration.FullDateFirstFilledComputation

/-! # Direct one-star full-Date `FirstFilledValue` computation locks -/

namespace A12Kernel.Conformance.FullDateFirstFilledComputation

open A12Kernel

private def dateField (id : FieldId) (groups : GroupPath) (name : String)
    (scope : List RepeatableLevel := [])
    (format : String := "yyyy-MM-dd")
    (youngerThan1900Check : Bool := false) : FlatFieldDecl := {
  id
  groupPath := groups
  name
  policy := { kind := .temporal .date TemporalComponents.fullDate }
  temporalTargetPolicy := some {
    format
    partialMode := .full
    youngerThan1900Check
  }
  repeatableScope := scope
}

private def target := dateField 1 ["Cart"] "FirstPromise"
private def source := dateField 2 ["Cart", "Lines"] "PromiseDate" [10]
private def dottedSource :=
  dateField 3 ["Cart", "Lines"] "DottedDate" [10] "dd.MM.yyyy"
private def checkedSource :=
  dateField 4 ["Cart", "Lines"] "CheckedDate" [10] "yyyy-MM-dd" true
private def timeSource : FlatFieldDecl := {
  id := 5
  groupPath := ["Cart", "Lines"]
  name := "Time"
  policy := { kind := .temporal .time TemporalComponents.time }
  temporalTargetPolicy := some { format := "HH:mm:ss" }
  repeatableScope := [10]
}
private def monthSource : FlatFieldDecl := {
  id := 10
  groupPath := ["Cart", "Lines"]
  name := "Month"
  policy := { kind := .temporal .date TemporalComponents.fullDate }
  temporalTargetPolicy := some {
    format := "MM"
    partialMode := .yearOptional
  }
  repeatableScope := [10]
}
private def partialSource : FlatFieldDecl := {
  dateField 11 ["Cart", "Lines"] "PartialDate" [10] with
    temporalTargetPolicy := some {
      format := "yyyy-MM-dd"
      partialMode := .yearOptional
    }
}
private def incompleteSource : FlatFieldDecl := {
  dateField 12 ["Cart", "Lines"] "IncompleteDate" [10] with
    policy := { kind := .temporal .date {
      year := true
      month := true
      day := false
      hour := false
      minute := false
      second := false
    } }
}
private def repeatedTarget :=
  dateField 6 ["Cart", "Lines"] "RepeatedTarget" [10]
private def nestedSource :=
  dateField 7 ["Cart", "Lines", "Details"] "NestedDate" [10, 20]
private def otherFormatTarget :=
  dateField 8 ["Cart"] "DottedTarget" [] "dd.MM.yyyy"
private def otherGroupTarget := dateField 9 ["Other"] "OtherDate"

private def model : FlatModel := {
  fields := [
    target, source, dottedSource, checkedSource, timeSource, monthSource,
    partialSource, incompleteSource, repeatedTarget, nestedSource,
    otherFormatTarget, otherGroupTarget]
  repeatableGroups := [
    { level := 10, path := ["Cart", "Lines"], repeatability := some 99 },
    { level := 20, path := ["Cart", "Lines", "Details"],
      repeatability := some 4 }]
  timeZoneId := "UTC"
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
  field := "NestedDate"
}

private def checkedAt? (declaringGroup : GroupPath) (targetField : FieldId)
    (authored : SurfaceStarFieldPath) :=
  (checkFullDateFirstFilledComputation
    model declaringGroup targetField authored).toOption

private def checked? (targetField : FieldId) (authored : SurfaceStarFieldPath) :=
  checkedAt? ["Cart"] targetField authored

private def prepared :
    PreparedFlatStringContext model builtinStringPatternCompiler :=
  (prepareFlatStringContext { now := { epochMillis := 0 } }
    builtinStringPatternCompiler model).toOption.get (by native_decide)

private def dateValue (epochMillis : Int) (year month day : Nat) : Value :=
  .temporal (.date {
    instant := { epochMillis }
    parts := { year, month, day }
    basis := .storedGregorian })

private structure SourceInput where
  row : Nat
  stored : String
  raw : RawCell

private def input? (sourceInputs : List SourceInput) :
    Option (CheckedDocument model) :=
  let sourceCells := sourceInputs.map fun input => {
    address := { field := source.id, path := [input.row] }
    stored := input.stored
    raw := input.raw
  }
  (checkDocument prepared "en_US" {
    instantiatedRows := [
      { group := 10, path := [1] },
      { group := 10, path := [2] }]
    cells := [{
      address := { field := target.id, path := [] }
      stored := "2000-01-01"
      raw := .parsed (dateValue 946684800000 2000 1 1)
    }] ++ sourceCells
  }).toOption

private def outcome? (sourceInputs : List SourceInput) :
    Option FullDateTargetOutcome := do
  let operation ← checked? target.id (star "PromiseDate")
  let input ← input? sourceInputs
  operation.execute input |>.toOption

private def signature? (sourceInputs : List SourceInput) :
    Option String := do
  let outcome ← outcome? sourceInputs
  pure (match outcome with
    | .noValue => "CLEARED"
    | .accepted stored => "VALUE|" ++ stored.text
    | .errored _ _ => "ERRORED"
    | .poison _ => "POISON")

/- The retained temporal-family probe Kernel-calibrates these exact empty, row-1, and leading-empty result signatures. -/
example :
    signature? [] = some "CLEARED" ∧
      signature? [{
        row := 1
        stored := "2024-03-20"
        raw := .parsed (dateValue 1710892800000 2024 3 20)
      }] = some "VALUE|2024-03-20" ∧
      signature? [{
        row := 2
        stored := "2024-03-20"
        raw := .parsed (dateValue 1710892800000 2024 3 20)
      }] = some "VALUE|2024-03-20" := by
  native_decide

/- The typed adapter retains the parsed instant rather than copying the source's stored text; this mechanism separator is internal, not Kernel-calibrated. -/
example :
    signature? [{
      row := 1
      stored := "2001-02-03"
      raw := .parsed (dateValue 1710892800000 2024 3 20)
    }] = some "VALUE|2024-03-20" := by
  native_decide

/- First-present and first-formal terminals both hide the suffix; these order branches remain externally uncalibrated. -/
example :
    signature? [
      {
        row := 1
        stored := "2024-03-20"
        raw := .parsed (dateValue 1710892800000 2024 3 20)
      },
      { row := 2, stored := "XX", raw := .rejected .malformed }
    ] = some "VALUE|2024-03-20" ∧
      signature? [
        { row := 1, stored := "XX", raw := .rejected .malformed },
        {
          row := 2
          stored := "2024-03-20"
          raw := .parsed (dateValue 1710892800000 2024 3 20)
        }
      ] = some "POISON" := by
  native_decide

/- The checked boundary admits only the bounded fixed `yyyy-MM-dd` full-Date target and direct single-level starred source. -/
example :
    (checked? target.id (star "PromiseDate")).isSome = true ∧
      (checked? target.id (star "DottedDate")).isNone = true ∧
      (checked? target.id (star "CheckedDate")).isNone = true ∧
      (checked? target.id (star "Time")).isNone = true ∧
      (checked? target.id (star "Month")).isNone = true ∧
      (checked? target.id (star "PartialDate")).isNone = true ∧
      (checked? target.id (star "IncompleteDate")).isNone = true ∧
      (checked? otherFormatTarget.id (star "PromiseDate")).isNone = true ∧
      (checked? otherGroupTarget.id (star "PromiseDate")).isNone = true ∧
      (checkedAt? ["Cart", "Lines"] repeatedTarget.id
        (star "PromiseDate")).isNone = true ∧
      (checked? target.id nestedStar).isNone = true := by
  native_decide

end A12Kernel.Conformance.FullDateFirstFilledComputation
