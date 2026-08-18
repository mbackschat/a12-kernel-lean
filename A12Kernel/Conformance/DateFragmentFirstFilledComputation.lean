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
private def yearSource :=
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
private def yearTarget := fragmentField 8 ["Review"] "FirstYear" [] "yyyy"
private def otherGroupTarget := fragmentField 9 ["Other"] "OtherMonth"
private def checkedSource : FlatFieldDecl := {
  fragmentField 10 ["Review", "Rows"] "CheckedMonth" [10] with
    temporalTargetPolicy := some {
      format := "MM"
      partialMode := .yearOptional
      youngerThan1900Check := true
    }
}
private def yearMonthTarget :=
  fragmentField 11 ["Review"] "FirstYearMonth" [] "yyyy-MM"
private def yearMonthSource :=
  fragmentField 12 ["Review", "Rows"] "YearMonth" [10] "yyyy-MM"
private def monthDayTarget :=
  fragmentField 13 ["Review"] "FirstMonthDay" [] "MM-dd"
private def monthDaySource :=
  fragmentField 14 ["Review", "Rows"] "MonthDay" [10] "MM-dd"
private def unsupportedTarget :=
  fragmentField 15 ["Review"] "Unsupported" [] "yyyyMM"
private def unsupportedSource :=
  fragmentField 16 ["Review", "Rows"] "UnsupportedSource" [10] "yyyyMM"

private def model : FlatModel := {
  fields := [
    target, source, yearSource, fullDate, time, repeatedTarget, nestedSource,
    yearTarget, otherGroupTarget, checkedSource, yearMonthTarget,
    yearMonthSource, monthDayTarget, monthDaySource, unsupportedTarget,
    unsupportedSource]
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

private def dateValue (year month day : Nat) : Value :=
  .temporal (.date {
    instant := { epochMillis := 0 }
    parts := { year, month, day }
    basis := .storedGregorian })

private def inputFor? (targetDeclaration sourceDeclaration : FlatFieldDecl)
    (sourceInput : Option (String × RawCell)) :
    Option (CheckedDocument model) :=
  let sourceCell := sourceInput.map fun (stored, raw) => {
    address := { field := sourceDeclaration.id, path := [1] }
    stored
    raw
  }
  (checkDocument prepared "en_US" {
    instantiatedRows := [{ group := 10, path := [1] }]
    cells := [{
      address := { field := targetDeclaration.id, path := [] }
      stored := "01"
      raw := .parsed (dateValue 2000 1 1)
    }] ++ sourceCell.toList
  }).toOption

private def resultFor? (targetDeclaration sourceDeclaration : FlatFieldDecl)
    (sourceInput : Option (String × RawCell)) :
    Option TokenComputationResult := do
  let operation ← checked? targetDeclaration.id (star sourceDeclaration.name)
  let input ← inputFor? targetDeclaration sourceDeclaration sourceInput
  operation.execute input |>.toOption

private def result? := resultFor? target source

/- The externally measured empty selection clears a seeded target, while the filled source yields the measured `MM` token. -/
example :
    result? none = some .noValue ∧
      result? (some ("06", .parsed (dateValue 2000 6 1))) =
        some (.value "06") := by
  native_decide

/- The other statically measured policies reuse the exact-token result domain. Their direct runtime compositions remain external-evidence pending. -/
example :
    resultFor? yearTarget yearSource
        (some ("2024", .parsed (dateValue 2024 1 1))) =
      some (.value "2024") ∧
    resultFor? yearMonthTarget yearMonthSource
        (some ("2024-03", .parsed (dateValue 2024 3 1))) =
      some (.value "2024-03") ∧
    resultFor? monthDayTarget monthDaySource
        (some ("03-20", .parsed (dateValue 2000 3 20))) =
      some (.value "03-20") := by
  native_decide

/- A reached formal rejection poisons through the checked cell; this branch remains externally uncalibrated. -/
example :
    result? (some ("XX", .rejected .malformed)) =
      some (.poison .malformed) := by
  native_decide

/- The checked boundary admits every measured legal DateFragment policy only when target and direct single-level starred source match exactly. -/
example :
    (checked? target.id (star "Month")).isSome = true ∧
      (checked? target.id (star "Year")).isNone = true ∧
      (checked? yearTarget.id (star "Year")).isSome = true ∧
      (checked? yearTarget.id (star "Month")).isNone = true ∧
      (checked? yearMonthTarget.id (star "YearMonth")).isSome = true ∧
      (checked? yearMonthTarget.id (star "MonthDay")).isNone = true ∧
      (checked? monthDayTarget.id (star "MonthDay")).isSome = true ∧
      (checked? monthDayTarget.id (star "YearMonth")).isNone = true ∧
      (checked? unsupportedTarget.id (star "UnsupportedSource")).isNone =
        true ∧
      (checked? target.id (star "Date")).isNone = true ∧
      (checked? target.id (star "Clock")).isNone = true ∧
      (checked? target.id (star "CheckedMonth")).isNone = true ∧
      (checked? otherGroupTarget.id (star "Month")).isNone = true ∧
      (checkedAt? ["Review", "Rows"] repeatedTarget.id
        (star "Month")).isNone = true ∧
      (checked? target.id nestedStar).isNone = true := by
  native_decide

end A12Kernel.Conformance.DateFragmentFirstFilledComputation
