import A12Kernel.Elaboration.FullDateComputationApplication
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
private def dottedTarget :=
  dateField 8 ["Cart"] "DottedTarget" [] "dd.MM.yyyy"
private def otherGroupTarget := dateField 9 ["Other"] "OtherDate"
private def unsupportedFormatTarget :=
  dateField 13 ["Cart"] "UnsupportedTarget" [] "yyyy/MM/dd"
private def unsupportedFormatSource :=
  dateField 14 ["Cart", "Lines"] "UnsupportedSource" [10] "yyyy/MM/dd"
private def checkedDottedSource :=
  dateField 15 ["Cart", "Lines"] "CheckedDottedSource" [10]
    "dd.MM.yyyy" true
private def checkedDottedTarget :=
  dateField 16 ["Cart"] "CheckedDottedTarget" [] "dd.MM.yyyy" true

private def model : FlatModel := {
  fields := [
    target, source, dottedSource, checkedSource, timeSource, monthSource,
    partialSource, incompleteSource, repeatedTarget, nestedSource,
    dottedTarget, otherGroupTarget, unsupportedFormatTarget,
    unsupportedFormatSource, checkedDottedSource, checkedDottedTarget]
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

private def checkedDocument? (cells : List ClassifiedCellInput) :
    Option (CheckedDocument model) :=
  (checkDocument prepared "en_US" {
    instantiatedRows := [
      { group := 10, path := [1] },
      { group := 10, path := [2] }]
    cells
  }).toOption

private def inputWithTargetFor? (targetDeclaration sourceDeclaration : FlatFieldDecl)
    (targetStored : String) (targetRaw : RawCell)
    (sourceInputs : List SourceInput)
    (extraCells : List ClassifiedCellInput := []) :
    Option (CheckedDocument model) :=
  let sourceCells := sourceInputs.map fun input => {
    address := { field := sourceDeclaration.id, path := [input.row] }
    stored := input.stored
    raw := input.raw
  }
  checkedDocument? ([{
    address := { field := targetDeclaration.id, path := [] }
    stored := targetStored
    raw := targetRaw
  }] ++ sourceCells ++ extraCells)

private def inputFor? (targetDeclaration sourceDeclaration : FlatFieldDecl)
    (sourceInputs : List SourceInput) :
    Option (CheckedDocument model) :=
  inputWithTargetFor? targetDeclaration sourceDeclaration
    "2000-01-01" (.parsed (dateValue 946684800000 2000 1 1))
    sourceInputs

private def outcomeFor? (targetDeclaration sourceDeclaration : FlatFieldDecl)
    (sourceInputs : List SourceInput) :
    Option FullDateTargetOutcome := do
  let operation ← checked? targetDeclaration.id (star sourceDeclaration.name)
  let input ← inputFor? targetDeclaration sourceDeclaration sourceInputs
  operation.execute input |>.toOption

private def outcome? := outcomeFor? target source

private def signatureFor? (targetDeclaration sourceDeclaration : FlatFieldDecl)
    (sourceInputs : List SourceInput) :
    Option String := do
  let outcome ← outcomeFor? targetDeclaration sourceDeclaration sourceInputs
  pure (match outcome with
    | .noValue => "CLEARED"
    | .accepted stored => "VALUE|" ++ stored.text
    | .errored _ _ => "ERRORED"
    | .poison _ => "POISON")

private def signature? := signatureFor? target source

private def runViewFor? (targetDeclaration sourceDeclaration : FlatFieldDecl)
    (targetStored : String) (targetRaw : RawCell)
    (sourceInputs : List SourceInput)
    (residualMessages : List FormalCause := []) :
    Option (FullDateComputationRunView FormalCause) := do
  let operation ← checked? targetDeclaration.id (star sourceDeclaration.name)
  let input ← inputWithTargetFor? targetDeclaration sourceDeclaration
    targetStored targetRaw sourceInputs
  operation.executeResult input residualMessages |>.toOption

private def selectedDate : StoredDate := ⟨"2024-03-20", by decide⟩
private def destinationDate : StoredDate := ⟨"2010-02-03", by decide⟩
private def unrelatedDate : StoredDate := ⟨"2024-04-01", by decide⟩

private def unrelatedCell : ClassifiedCellInput := {
  address := { field := otherGroupTarget.id, path := [] }
  stored := unrelatedDate.text
  raw := .parsed (dateValue 1711929600000 2024 4 1)
}

private def destinationFor? (includeTarget : Bool) :
    Option (CheckedDocument model) :=
  let targetCells := if includeTarget then [{
    address := { field := target.id, path := [] }
    stored := destinationDate.text
    raw := .parsed (dateValue 1265155200000 2010 2 3)
  }] else []
  checkedDocument? (targetCells ++ [unrelatedCell])

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

/- The checked FirstFilled operation classifies its typed target outcome against the immutable source, then applies only the retained change to a separate checked destination while preserving unrelated state. -/
example : (do
    let view ← runViewFor? target source "2000-01-01"
      (.parsed (dateValue 946684800000 2000 1 1)) [{
        row := 1
        stored := selectedDate.text
        raw := .parsed (dateValue 1710892800000 2024 3 20)
      }]
    let destination ← destinationFor? true
    let applied ← view.applyToChecked destination |>.toOption
    pure (view.withoutErrors, view.withChanges,
      applied target.id, applied otherGroupTarget.id)) =
    some ([{ targetField := target.id, value := selectedDate }],
      [{ targetField := target.id, value := selectedDate }],
      .presentValue selectedDate, .presentValue unrelatedDate) := by
  native_decide

/- Change classification remains source-relative: a result equal to the source target is public but inert against a different destination target. -/
example : (do
    let view ← runViewFor? target source selectedDate.text
      (.parsed (dateValue 1710892800000 2024 3 20)) [{
        row := 1
        stored := selectedDate.text
        raw := .parsed (dateValue 1710892800000 2024 3 20)
      }]
    let destination ← destinationFor? true
    let applied ← view.applyToChecked destination |>.toOption
    pure (view.withoutErrors, view.withChanges, applied target.id)) =
    some ([{ targetField := target.id, value := selectedDate }], [],
      .presentValue destinationDate) := by
  native_decide

/- Exhaustion and a reached formal cause both retain a source-filled clear. Application materializes an absent destination target as present-empty without disturbing unrelated state. -/
example :
    (do
      let view ← runViewFor? target source "2000-01-01"
        (.parsed (dateValue 946684800000 2000 1 1)) []
      let destination ← destinationFor? false
      let applied ← view.applyToChecked destination |>.toOption
      pure (view.cleared, view.noErrorOccurred,
        applied target.id, applied otherGroupTarget.id)) =
      some ([target.id], true, .presentEmpty, .presentValue unrelatedDate) ∧
    (do
      let view ← runViewFor? target source "2000-01-01"
        (.parsed (dateValue 946684800000 2000 1 1)) [{
          row := 1
          stored := "XX"
          raw := .rejected .malformed
        }]
      let destination ← destinationFor? false
      let applied ← view.applyToChecked destination |>.toOption
      pure (view.cleared, view.noErrorOccurred,
        applied target.id, applied otherGroupTarget.id)) =
      some ([target.id], true, .presentEmpty, .presentValue unrelatedDate) := by
  native_decide

/- The typed adapter retains the parsed instant rather than copying the source's stored text; this mechanism separator is internal, not Kernel-calibrated. -/
example :
    signature? [{
      row := 1
      stored := "2001-02-03"
      raw := .parsed (dateValue 1710892800000 2024 3 20)
    }] = some "VALUE|2024-03-20" := by
  native_decide

/- The second bounded full-Date declaration retains the same typed instant and delegates its exact dotted result to the target-owned renderer. Its direct `FirstFilledValue` composition remains external-evidence pending. -/
example :
    signatureFor? dottedTarget dottedSource [{
      row := 1
      stored := "copied-text-would-be-wrong"
      raw := .parsed (dateValue 1710892800000 2024 3 20)
    }] = some "VALUE|20.03.2024" := by
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

/- The checked boundary admits either exact full-Date format only when target and direct single-level starred source match; optional checks and wider profiles remain excluded. Placement is unconstrained: this shape's target is fixed and its operand is a star aggregate, so no iteration is derived and the Kernel admits the target from an unrelated sibling group — measured at the [fixed-target star placement checkpoint](../../docs/SOURCES.md#src-fixed-target-star-placement). A repeatable target is still refused, on the carrier's own fixed-target gate rather than on placement. -/
example :
    (checked? target.id (star "PromiseDate")).isSome = true ∧
      (checked? target.id (star "DottedDate")).isNone = true ∧
      (checked? dottedTarget.id (star "PromiseDate")).isNone = true ∧
      (checked? dottedTarget.id (star "DottedDate")).isSome = true ∧
      (checked? target.id (star "CheckedDate")).isNone = true ∧
      (checked? dottedTarget.id (star "CheckedDottedSource")).isNone = true ∧
      (checked? checkedDottedTarget.id (star "DottedDate")).isNone = true ∧
      (checked? unsupportedFormatTarget.id
        (star "UnsupportedSource")).isNone = true ∧
      (checked? target.id (star "Time")).isNone = true ∧
      (checked? target.id (star "Month")).isNone = true ∧
      (checked? target.id (star "PartialDate")).isNone = true ∧
      (checked? target.id (star "IncompleteDate")).isNone = true ∧
      (checked? otherGroupTarget.id (star "PromiseDate")).isSome = true ∧
      (checkedAt? ["Cart", "Lines"] repeatedTarget.id
        (star "PromiseDate")).isNone = true ∧
      (checked? target.id nestedStar).isNone = true := by
  native_decide

end A12Kernel.Conformance.FullDateFirstFilledComputation
