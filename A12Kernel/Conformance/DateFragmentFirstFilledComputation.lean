import A12Kernel.Elaboration.DateFragmentFirstFilledComputation
import A12Kernel.Elaboration.StringComputationRunApplication

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

private def rootFragmentCell (declaration : FlatFieldDecl)
    (stored : String) (month : Nat) : ClassifiedCellInput := {
  address := { field := declaration.id, path := [] }
  stored
  raw := .parsed (dateValue 2000 month 1)
}

private def destinationFor? (targetInput : Option (String × Nat))
    (otherInput : String × Nat := ("04", 4)) :
    Option (CheckedDocument model) :=
  (checkDocument prepared "en_US" {
    instantiatedRows := []
    cells := (targetInput.map fun (stored, month) =>
      rootFragmentCell target stored month).toList ++
      [rootFragmentCell otherGroupTarget otherInput.1 otherInput.2]
  }).toOption

private structure ResultApplicationSummary where
  targetField : FieldId
  values : List (FieldId × String)
  changes : List (FieldId × String)
  hasTargetErrors : Bool
  cleared : List FieldId
  residual : List FormalCause
  targetState : StringTargetState
  otherState : StringTargetState
  deriving Repr, DecidableEq

private def resultApplicationSummary?
    (sourceInput : Option (String × RawCell))
    (destination : CheckedDocument model)
    (residualMessages : List FormalCause := []) :
    Option ResultApplicationSummary := do
  let operation ← checked? target.id (star source.name)
  let input ← inputFor? target source sourceInput
  let result ← operation.executeResult input residualMessages |>.toOption
  let applied ← result.applyToChecked destination |>.toOption
  pure {
    targetField := result.operation.targetField
    values := result.string.withoutErrors.map fun item =>
      (item.targetField, item.value.text)
    changes := result.string.withChanges.map fun item =>
      (item.targetField, item.value.text)
    hasTargetErrors := !result.string.withErrors.isEmpty
    cleared := result.string.cleared
    residual := result.string.formalErrorsInOperands
    targetState := applied target.id
    otherState := applied otherGroupTarget.id
  }

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

/- A selected exact token is source-relative changed, retains residual messages, and applies only to its certified target in a separate same-model destination. -/
example : (do
    let destination ← destinationFor? (some ("03", 3))
    resultApplicationSummary?
      (some ("06", .parsed (dateValue 2000 6 1)))
      destination [.malformed]) = some {
        targetField := target.id
        values := [(target.id, "06")]
        changes := [(target.id, "06")]
        hasTargetErrors := false
        cleared := []
        residual := [.malformed]
        targetState := .presentValue ⟨"06", by decide⟩
        otherState := .presentValue ⟨"04", by decide⟩
      } := by
  native_decide

/- Source-identical selection remains inert against a destination carrying a different token. -/
example : (do
    let destination ← destinationFor? (some ("03", 3))
    resultApplicationSummary?
      (some ("01", .parsed (dateValue 2000 1 1))) destination) = some {
        targetField := target.id
        values := [(target.id, "01")]
        changes := []
        hasTargetErrors := false
        cleared := []
        residual := []
        targetState := .presentValue ⟨"03", by decide⟩
        otherState := .presentValue ⟨"04", by decide⟩
      } := by
  native_decide

/- Exhaustion clears a source-filled target and retained clearing materializes an absent destination target as present-empty. -/
example : (do
    let destination ← destinationFor? none
    resultApplicationSummary? none destination) = some {
        targetField := target.id
        values := []
        changes := []
        hasTargetErrors := false
        cleared := [target.id]
        residual := []
        targetState := .presentEmpty
        otherState := .presentValue ⟨"04", by decide⟩
      } := by
  native_decide

/- Reached source poison is cause-blind at the result boundary and clears without manufacturing a target error. -/
example : (do
    let destination ← destinationFor? (some ("03", 3))
    resultApplicationSummary?
      (some ("XX", .rejected .malformed)) destination) = some {
        targetField := target.id
        values := []
        changes := []
        hasTargetErrors := false
        cleared := [target.id]
        residual := []
        targetState := .presentEmpty
        otherState := .presentValue ⟨"04", by decide⟩
      } := by
  native_decide

/- The checked boundary admits every measured legal DateFragment policy only when target and direct single-level starred source match exactly. Placement is unconstrained. Declaring at the source's own repeatable group puts the fixed target *above* the declaring group, which the checkpoint's `star-rowgroup` row measures as admitted: a star aggregate derives no iteration, so the Kernel's containment gate cannot fire. An unrepresentable declaring group is still refused. Varying the declaring group rather than the target's group keeps the fixture to one model root, as an authored A12 model is. -/
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
      (checkedAt? ["Review", "Rows"] target.id (star "Month")).isSome = true ∧
      (checkedAt? [] target.id (star "Month")).isNone = true ∧
      (checkedAt? ["Review", "Rows"] repeatedTarget.id
        (star "Month")).isNone = true ∧
      (checked? target.id nestedStar).isNone = true := by
  native_decide

end A12Kernel.Conformance.DateFragmentFirstFilledComputation
