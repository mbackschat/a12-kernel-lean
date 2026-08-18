import A12Kernel.Elaboration.DateRangeFirstFilledComputation
import A12Kernel.Semantics.TemporalApplication

/-! # Direct one-star DateRange `FirstFilledValue` computation locks -/

namespace A12Kernel.Conformance.DateRangeFirstFilledComputation

open A12Kernel

private def rangeField (id : FieldId) (groupPath : GroupPath) (name : String)
    (scope : List RepeatableLevel := []) (format : String := "yyyy-MM-dd")
    (separator : String := "/") : FlatFieldDecl := {
  id
  groupPath
  name
  policy := { kind := .dateRange }
  dateRangePolicy := some { format, separator }
  repeatableScope := scope
}

private def target := rangeField 1 ["Cart"] "FirstWindow"
private def source := rangeField 2 ["Cart", "Lines"] "Window" [10]
private def otherFormatSource :=
  rangeField 3 ["Cart", "Lines"] "DottedWindow" [10] "dd.MM.yyyy" "-"
private def otherSeparatorTarget :=
  rangeField 4 ["Cart"] "DashedWindow" [] "yyyy-MM-dd" "-"
private def otherSeparatorSource :=
  rangeField 5 ["Cart", "Lines"] "DashedSource" [10] "yyyy-MM-dd" "-"
private def dottedTarget :=
  rangeField 6 ["Cart"] "DottedTarget" [] "dd.MM.yyyy" "-"
private def dottedSource :=
  rangeField 7 ["Cart", "Lines"] "DottedSource" [10] "dd.MM.yyyy" "-"
private def unsupportedDottedTarget :=
  rangeField 8 ["Cart"] "UnsupportedDottedTarget" [] "dd.MM.yyyy" "/"
private def unsupportedDottedSource :=
  rangeField 9 ["Cart", "Lines"] "UnsupportedDottedSource" [10]
    "dd.MM.yyyy" "/"

private def model : FlatModel := {
  fields := [target, source, otherFormatSource, otherSeparatorTarget,
    otherSeparatorSource, dottedTarget, dottedSource, unsupportedDottedTarget,
    unsupportedDottedSource]
  repeatableGroups := [
    { level := 10, path := ["Cart", "Lines"], repeatability := some 99 }]
  timeZoneId := "UTC"
}

private def star (field : String) : SurfaceStarFieldPath := {
  base := .absolute
  groups := [{ name := "Cart" }, { name := "Lines", starred := true }]
  field
}

private def checked? (targetField : FieldId) (field : String) :=
  (checkDateRangeFirstFilledComputation
    model ["Cart"] targetField (star field)).toOption

private def prepared :
    PreparedFlatStringContext model builtinStringPatternCompiler :=
  (prepareFlatStringContext { now := { epochMillis := 0 } }
    builtinStringPatternCompiler model).toOption.get (by native_decide)

private def dateValue (epochMillis : Int) (year month day : Nat) : DateValue := {
  instant := { epochMillis }
  parts := { year, month, day }
  basis := .storedGregorian
}

private def rangeValue (startMillis finishMillis : Int)
    (startDay finishDay : Nat) : DateRangeValue := {
  start := dateValue startMillis 2024 3 startDay
  finish := dateValue finishMillis 2024 3 finishDay
}

private structure SourceInput where
  row : Nat
  stored : String
  raw : RawCell

private def inputFor? (targetDeclaration sourceDeclaration : FlatFieldDecl)
    (sourceInputs : List SourceInput) :
    Option (CheckedDocument model) :=
  let sourceCells := sourceInputs.map fun input => {
    address := { field := sourceDeclaration.id, path := [input.row] }
    stored := input.stored
    raw := input.raw
  }
  (checkDocument prepared "en_US" {
    instantiatedRows := [
      { group := 10, path := [1] }, { group := 10, path := [2] }]
    cells := [{
      address := { field := targetDeclaration.id, path := [] }
      stored := "2000-01-01/2000-01-02"
      raw := .parsed (.dateRange
        (rangeValue 946684800000 946771200000 1 2))
    }] ++ sourceCells
  }).toOption

private def executionFor? (targetDeclaration sourceDeclaration : FlatFieldDecl)
    (sourceInputs : List SourceInput) :
    Option (Except DateRangeFirstFilledComputationFault DateRangeTargetOutcome) := do
  let operation ← checked? targetDeclaration.id sourceDeclaration.name
  let input ← inputFor? targetDeclaration sourceDeclaration sourceInputs
  pure (operation.execute input)

private def execution? := executionFor? target source

private def signatureFor? (targetDeclaration sourceDeclaration : FlatFieldDecl)
    (sourceInputs : List SourceInput) : Option String := do
  let execution ← executionFor? targetDeclaration sourceDeclaration sourceInputs
  let outcome ← execution.toOption
  pure (match outcome with
    | .noValue => "CLEARED"
    | .accepted stored => "VALUE|" ++ stored.text
    | .poison _ => "POISON")

private def signature? := signatureFor? target source

private def unresolvedEndpoint? (sourceInputs : List SourceInput) :
    Option DateRangeValue := do
  let execution ← execution? sourceInputs
  match execution with
  | .error (.unresolvedEndpoint range) => some range
  | .error (.source _) | .ok _ => none

private def selectedRange := rangeValue 1710892800000 1710979200000 20 21
private def invalidRange : DateRangeValue := {
  selectedRange with
  finish := { selectedRange.finish with
    parts := { year := 2024, month := 2, day := 30 } }
}

private def invalidInput : List SourceInput := [{
  row := 1
  stored := "2024-03-20/2024-02-30"
  raw := .parsed (.dateRange invalidRange)
}]

/- The retained temporal-family probe Kernel-calibrates these exact all-empty and first-row-filled result signatures. -/
example :
    signature? [] = some "CLEARED" ∧
      signature? [{
        row := 1
        stored := "2024-03-20/2024-03-21"
        raw := .parsed (.dateRange selectedRange)
      }] = some "VALUE|2024-03-20/2024-03-21" := by
  native_decide

/- Typed endpoints, not the source token, supply the rendered target value; this mechanism separator is internal rather than externally calibrated. -/
example :
    signature? [{
      row := 1
      stored := "2001-02-03/2001-02-04"
      raw := .parsed (.dateRange selectedRange)
    }] = some "VALUE|2024-03-20/2024-03-21" := by
  native_decide

/- The second exact legal declaration pair selects the same typed endpoints but renders through the target-owned dotted/dash policy. Static admission and the renderer are externally established separately; their direct `FirstFilledValue` composition remains external-evidence pending. -/
example :
    signatureFor? dottedTarget dottedSource [{
      row := 1
      stored := "copied-text-would-be-wrong"
      raw := .parsed (.dateRange selectedRange)
    }] = some "VALUE|20.03.2024-21.03.2024" := by
  native_decide

/- A reached formal cause terminates before a later present range. -/
example :
    signature? [
      { row := 1, stored := "XX", raw := .rejected .malformed },
      {
        row := 2
        stored := "2024-03-20/2024-03-21"
        raw := .parsed (.dateRange selectedRange)
      }
    ] = some "POISON" := by
  native_decide

/- The universal value remains wider than the resolved target bridge. -/
example :
    (execution? invalidInput).isSome = true ∧
      unresolvedEndpoint? invalidInput = some invalidRange := by
  native_decide

/- Both declarations must share one exact admitted DateRange pair; crossing the two legal pairs or changing only the ISO separator remains refused. -/
example :
    (checked? target.id "Window").isSome = true ∧
      (checked? target.id "DottedWindow").isNone = true ∧
      (checked? dottedTarget.id "Window").isNone = true ∧
      (checked? dottedTarget.id "DottedSource").isSome = true ∧
      (checked? target.id "DashedSource").isNone = true ∧
      (checked? otherSeparatorTarget.id "Window").isNone = true ∧
      (checked? unsupportedDottedTarget.id "UnsupportedDottedSource").isNone =
        true := by
  native_decide

private def storedRange : StoredDateRange := {
  text := "2024-03-20/2024-03-21"
  nonempty := by decide
}

/- DateRange specializes the existing exact value/clear transition without entering scalar temporal indexing. -/
example :
    (DateRangeTargetOutcome.accepted storedRange).applyTo .presentEmpty =
        .presentValue storedRange ∧
      DateRangeTargetOutcome.noValue.applyTo .absent = .absent ∧
      DateRangeTargetOutcome.noValue.applyTo (.presentValue storedRange) =
        .presentEmpty := by
  decide

end A12Kernel.Conformance.DateRangeFirstFilledComputation
