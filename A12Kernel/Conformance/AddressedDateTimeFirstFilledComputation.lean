import A12Kernel.Elaboration.AddressedDateTimeFirstFilledComputation

/-! # Exact-address repeatable DateTime `FirstFilledValue` locks -/

namespace A12Kernel.Conformance.AddressedDateTimeFirstFilledComputation

open A12Kernel

private def dateTimeField (id : FieldId) (name : String)
    (groupPath : GroupPath) (scope : List RepeatableLevel)
    (format : String := "yyyy-MM-dd'T'HH:mm:ss")
    (components : TemporalComponents := TemporalComponents.now) : FlatFieldDecl := {
  id, name, groupPath, repeatableScope := scope
  policy := { kind := .temporal .dateTime components }
  temporalTargetPolicy := some { format }
}

private def source := dateTimeField 1 "Stamp"
  ["Projects", "Choices"] [10, 20]
private def timeSource : FlatFieldDecl := {
  id := 2, name := "Clock", groupPath := ["Projects", "Choices"]
  repeatableScope := [10, 20]
  policy := { kind := .temporal .time TemporalComponents.time }
  temporalTargetPolicy := some { format := "HH:mm:ss" }
}
private def incompleteSource := dateTimeField 3 "IncompleteStamp"
  ["Projects", "Choices"] [10, 20] "yyyy-MM-dd'T'HH:mm:ss"
  { TemporalComponents.now with second := false }
private def target := dateTimeField 4 "SelectedStamp"
  ["Projects", "Tasks"] [10, 30]
private def incompleteTarget := dateTimeField 5 "IncompleteTarget"
  ["Projects", "Tasks"] [10, 30] "yyyy-MM-dd'T'HH:mm:ss"
  { TemporalComponents.now with second := false }
private def fixedTarget := dateTimeField 6 "FixedStamp" ["Summary"] []
private def unrelated := dateTimeField 7 "UnrelatedStamp" ["Summary"] []

private def model : FlatModel := {
  fields := [source, timeSource, incompleteSource, target, incompleteTarget,
    fixedTarget, unrelated]
  repeatableGroups := [
    { level := 10, path := ["Projects"], repeatability := some 4 },
    { level := 20, path := ["Projects", "Choices"], repeatability := some 3 },
    { level := 30, path := ["Projects", "Tasks"], repeatability := some 3 }]
  timeZoneId := "Europe/Berlin"
}

private def siblingStar (field : String) : SurfaceStarFieldPath := {
  base := .relative 1
  groups := [{ name := "Choices", starred := true }]
  field
}

private def operation? :
    Option (CheckedAddressedDateTimeFirstFilledComputation model) :=
  (checkAddressedDateTimeFirstFilledComputation model
    ["Projects", "Tasks"] target.id (siblingStar source.name)).toOption

private def elabError? (checked : Except
    AddressedDateTimeFirstFilledComputationElabError
    (CheckedAddressedDateTimeFirstFilledComputation model)) :=
  match checked with
  | .error cause => some cause
  | .ok _ => none

/- The checked boundary admits only a complete ISO DateTime source and target, and the target must be repeatable. -/
example : operation?.isSome = true ∧
    elabError? (checkAddressedDateTimeFirstFilledComputation model
      ["Projects", "Tasks"] target.id
      (siblingStar timeSource.name)) =
        some (.sourceCarrier timeSource.path) ∧
    elabError? (checkAddressedDateTimeFirstFilledComputation model
      ["Projects", "Tasks"] target.id
      (siblingStar incompleteSource.name)) =
        some (.sourceCarrier incompleteSource.path) ∧
    elabError? (checkAddressedDateTimeFirstFilledComputation model
      ["Projects", "Tasks"] incompleteTarget.id
      (siblingStar source.name)) =
        some (.targetPolicy (.components incompleteTarget.id
          { TemporalComponents.now with second := false })) ∧
    elabError? (checkAddressedDateTimeFirstFilledComputation model
      ["Summary"] fixedTarget.id (siblingStar source.name)) =
        some (.targetNotRepeatable fixedTarget.path) := by
  native_decide

private def prepared :
    PreparedFlatStringContext model builtinStringPatternCompiler :=
  (prepareFlatStringContext { now := { epochMillis := 0 } }
    builtinStringPatternCompiler model).toOption.get (by native_decide)

private def clock (hour minute second : Nat)
    (valid : hour < 24 ∧ minute < 60 ∧ second < 60) : TimeOfDay :=
  ⟨hour, minute, second, valid⟩

private def dateTimeValue (epochMillis : Int) (year : Int)
    (month day hour minute second : Nat)
    (valid : hour < 24 ∧ minute < 60 ∧ second < 60) : RawCell :=
  .parsed (.temporal (.dateTime { epochMillis } { year, month, day }
    (clock hour minute second valid) .storedGregorian))

private def rows : List RowAddr := [
  { group := 10, path := [1] }, { group := 10, path := [2] },
  { group := 10, path := [3] }, { group := 10, path := [4] },
  { group := 20, path := [1, 1] }, { group := 20, path := [1, 2] },
  { group := 20, path := [2, 1] }, { group := 20, path := [4, 1] },
  { group := 20, path := [4, 2] },
  { group := 30, path := [1, 1] }, { group := 30, path := [1, 2] },
  { group := 30, path := [2, 1] }, { group := 30, path := [3, 1] },
  { group := 30, path := [4, 1] }]

private def cell (field : FieldId) (path : List Nat) (stored : String)
    (raw : RawCell) : ClassifiedCellInput := {
  address := { field, path }, stored, raw
}

private def address (field : FieldId) (path : List Nat) : CellAddr :=
  { field, path }

private def document? (cells : List ClassifiedCellInput) :
    Option (CheckedDocument model) :=
  (checkDocument prepared "en_US" { instantiatedRows := rows, cells }).toOption

private def input? : Option (CheckedDocument model) := document? [
  cell source.id [1, 2] "2001-02-03T04:05:06"
    (dateTimeValue 1717229472000 2001 2 3 4 5 6 (by decide)),
  cell source.id [2, 1] "2024-07-01T13:14:15"
    (dateTimeValue 1719832455000 2024 7 1 13 14 15 (by decide)),
  cell source.id [4, 1] "bad" (.rejected .dateFormat),
  cell source.id [4, 2] "2024-08-01T16:17:18"
    (dateTimeValue 1722521838000 2024 8 1 16 17 18 (by decide)),
  cell target.id [1, 1] "2024-06-01T10:11:12"
    (dateTimeValue 1717229472000 2024 6 1 10 11 12 (by decide)),
  cell target.id [1, 2] "2000-01-01T12:34:56"
    (dateTimeValue 946726496000 2000 1 1 12 34 56 (by decide)),
  cell target.id [3, 1] "2000-01-01T12:34:56"
    (dateTimeValue 946726496000 2000 1 1 12 34 56 (by decide)),
  cell target.id [4, 1] "2000-01-01T12:34:56"
    (dateTimeValue 946726496000 2000 1 1 12 34 56 (by decide))]

private def stored (text : String) (nonempty : text ≠ "" := by decide) :
    StoredDateTime := { text, nonempty }

/- Every physical target row scans only its enclosing project's sibling source extent, renders the selected instant in the model zone, and retains its exact target address. -/
example : (do
    let operation ← operation?
    let input ← input?
    let outcomes ← operation.execute input |>.toOption
    pure (outcomes.map fun entry => (entry.targetField, entry.outcome))) = some [
      (address target.id [1, 1], .accepted (stored "2024-06-01T10:11:12")),
      (address target.id [1, 2], .accepted (stored "2024-06-01T10:11:12")),
      (address target.id [2, 1], .accepted (stored "2024-07-01T13:14:15")),
      (address target.id [3, 1], .noValue),
      (address target.id [4, 1], .poison .dateFormat)] := by
  native_decide

private structure ResultApplicationSummary where
  values : List (CellAddr × String)
  changes : List (CellAddr × String)
  cleared : List CellAddr
  residual : List FormalCause
  row11 : DateTimeTargetState
  row12 : DateTimeTargetState
  row21 : DateTimeTargetState
  row31 : DateTimeTargetState
  row41 : DateTimeTargetState
  unrelatedState : DateTimeTargetState
  deriving Repr, DecidableEq

private def resultApplicationSummary? : Option ResultApplicationSummary := do
  let operation ← operation?
  let input ← input?
  let destination ← document? [
    cell target.id [1, 1] "2000-01-01T12:34:56"
      (dateTimeValue 946726496000 2000 1 1 12 34 56 (by decide)),
    cell unrelated.id [] "2024-04-01T06:00:00"
      (dateTimeValue 1711944000000 2024 4 1 6 0 0 (by decide))]
  let result ← operation.executeResult input [.dateFormat] |>.toOption
  let applied ← result.applyToChecked destination |>.toOption
  pure {
    values := result.dateTime.withoutErrors.map fun item =>
      (item.targetField, item.value.text)
    changes := result.dateTime.withChanges.map fun item =>
      (item.targetField, item.value.text)
    cleared := result.dateTime.cleared
    residual := result.dateTime.formalErrorsInOperands
    row11 := applied (address target.id [1, 1])
    row12 := applied (address target.id [1, 2])
    row21 := applied (address target.id [2, 1])
    row31 := applied (address target.id [3, 1])
    row41 := applied (address target.id [4, 1])
    unrelatedState := applied (address unrelated.id [])
  }

/- Result classification stays source-relative, while application mutates only retained exact-address actions in the separate destination projection. -/
example : resultApplicationSummary? = some {
    values := [
      (address target.id [1, 1], "2024-06-01T10:11:12"),
      (address target.id [1, 2], "2024-06-01T10:11:12"),
      (address target.id [2, 1], "2024-07-01T13:14:15")]
    changes := [
      (address target.id [1, 2], "2024-06-01T10:11:12"),
      (address target.id [2, 1], "2024-07-01T13:14:15")]
    cleared := [address target.id [3, 1], address target.id [4, 1]]
    residual := [.dateFormat]
    row11 := .presentValue (stored "2000-01-01T12:34:56")
    row12 := .presentValue (stored "2024-06-01T10:11:12")
    row21 := .presentValue (stored "2024-07-01T13:14:15")
    row31 := .presentEmpty
    row41 := .presentEmpty
    unrelatedState := .presentValue (stored "2024-04-01T06:00:00")
  } := by
  native_decide

end A12Kernel.Conformance.AddressedDateTimeFirstFilledComputation
