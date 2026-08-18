import A12Kernel.Elaboration.DateFragmentFirstFilledComputation

/-! # Direct one-star DateFragment `FirstFilledValue` computation locks -/

namespace A12Kernel.Conformance.DateFragmentFirstFilledComputation

open A12Kernel

private def fragmentField (id : FieldId) (groups : GroupPath) (name : String)
    (scope : List RepeatableLevel := []) (format : String := "MM") :
    FlatFieldDecl := {
  id
  groupPath := groups
  name
  policy := { kind := .temporal .date TemporalComponents.fullDate }
  temporalTargetPolicy := some {
    format
    partialMode := .yearOptional
  }
  repeatableScope := scope
}

private def target := fragmentField 1 ["Review"] "FirstMonth"
private def source := fragmentField 2 ["Review", "Rows"] "Month" [10]
private def otherFormat :=
  fragmentField 3 ["Review", "Rows"] "Year" [10] "yyyy"
private def fullDate : FlatFieldDecl := {
  fragmentField 4 ["Review", "Rows"] "Date" [10] with
    temporalTargetPolicy := some { format := "MM" }
}
private def time : FlatFieldDecl := {
  id := 5
  groupPath := ["Review", "Rows"]
  name := "Clock"
  policy := { kind := .temporal .time TemporalComponents.time }
  temporalTargetPolicy := some { format := "MM" }
  repeatableScope := [10]
}
private def repeatedTarget :=
  fragmentField 6 ["Review", "Rows"] "RepeatedMonth" [10]
private def nestedSource :=
  fragmentField 7 ["Review", "Rows", "Details"] "NestedMonth" [10, 20]
private def otherTarget := fragmentField 8 ["Review"] "FirstYear" [] "yyyy"
private def otherGroupTarget := fragmentField 9 ["Other"] "OtherMonth"
private def checkedSource : FlatFieldDecl := {
  fragmentField 10 ["Review", "Rows"] "CheckedMonth" [10] with
    temporalTargetPolicy := some {
      format := "MM"
      partialMode := .yearOptional
      youngerThan1900Check := true
    }
}

private def model : FlatModel := {
  fields := [
    target, source, otherFormat, fullDate, time, repeatedTarget, nestedSource,
    otherTarget, otherGroupTarget, checkedSource]
  repeatableGroups := [
    { level := 10, path := ["Review", "Rows"], repeatability := some 4 },
    { level := 20, path := ["Review", "Rows", "Details"],
      repeatability := some 3 }]
}

private def star (field : String) : SurfaceStarFieldPath := {
  base := .absolute
  groups := [{ name := "Review" }, { name := "Rows", starred := true }]
  field
}

private def nestedStar : SurfaceStarFieldPath := {
  base := .absolute
  groups := [
    { name := "Review" },
    { name := "Rows", starred := true },
    { name := "Details", starred := true }]
  field := "NestedMonth"
}

private def checkedAt? (declaringGroup : GroupPath) (targetField : FieldId)
    (authored : SurfaceStarFieldPath) :=
  (checkDateFragmentFirstFilledComputation
    model declaringGroup targetField authored).toOption

private def checked? (targetField : FieldId) (authored : SurfaceStarFieldPath) :=
  checkedAt? ["Review"] targetField authored

private def prepared :
    PreparedFlatStringContext model builtinStringPatternCompiler :=
  (prepareFlatStringContext { now := { epochMillis := 0 } }
    builtinStringPatternCompiler model).toOption.get (by native_decide)

private def dateValue (month : Nat) : Value :=
  .temporal (.date {
    instant := { epochMillis := 0 }
    parts := { year := 2000, month, day := 1 }
    basis := .storedGregorian })

private def input? (sourceInput : Option (String × RawCell)) :
    Option (CheckedDocument model) :=
  let sourceCell := sourceInput.map fun (stored, raw) => {
    address := { field := source.id, path := [1] }
    stored
    raw
  }
  (checkDocument prepared "en_US" {
    instantiatedRows := [{ group := 10, path := [1] }]
    cells := [{
      address := { field := target.id, path := [] }
      stored := "01"
      raw := .parsed (dateValue 1)
    }] ++ sourceCell.toList
  }).toOption

private def result? (sourceInput : Option (String × RawCell)) :
    Option TokenComputationResult := do
  let operation ← checked? target.id (star "Month")
  let input ← input? sourceInput
  operation.execute input |>.toOption

/- The externally measured empty selection clears a seeded target, while the filled source yields the measured `MM` token. -/
example :
    result? none = some .noValue ∧
      result? (some ("06", .parsed (dateValue 6))) = some (.value "06") := by
  native_decide

/- A reached formal rejection poisons through the checked cell; this branch remains externally uncalibrated. -/
example :
    result? (some ("XX", .rejected .malformed)) =
      some (.poison .malformed) := by
  native_decide

/- The checked boundary admits only the measured `MM` DateFragment carrier on a fixed target and direct single-level starred source. -/
example :
    (checked? target.id (star "Month")).isSome = true ∧
      (checked? target.id (star "Year")).isNone = true ∧
      (checked? target.id (star "Date")).isNone = true ∧
      (checked? target.id (star "Clock")).isNone = true ∧
      (checked? target.id (star "CheckedMonth")).isNone = true ∧
      (checked? otherTarget.id (star "Month")).isNone = true ∧
      (checked? otherGroupTarget.id (star "Month")).isNone = true ∧
      (checkedAt? ["Review", "Rows"] repeatedTarget.id
        (star "Month")).isNone = true ∧
      (checked? target.id nestedStar).isNone = true := by
  native_decide

end A12Kernel.Conformance.DateFragmentFirstFilledComputation
