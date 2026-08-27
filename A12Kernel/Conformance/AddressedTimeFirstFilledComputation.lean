import A12Kernel.Elaboration.AddressedTimeFirstFilledComputation

/-! # Exact-address repeatable Time `FirstFilledValue` locks -/

namespace A12Kernel.Conformance.AddressedTimeFirstFilledComputation

open A12Kernel

private def timeField (id : FieldId) (name : String)
    (groupPath : GroupPath) (scope : List RepeatableLevel)
    (format : String := "HH:mm:ss") : FlatFieldDecl := {
  id, name, groupPath, repeatableScope := scope
  policy := { kind := .temporal .time TemporalComponents.time }
  temporalTargetPolicy := some { format }
}

private def source := timeField 1 "Clock" ["Projects", "Choices"] [10, 20]
private def dateTimeSource : FlatFieldDecl := {
  id := 2, name := "Stamp", groupPath := ["Projects", "Choices"]
  repeatableScope := [10, 20]
  policy := { kind := .temporal .dateTime TemporalComponents.now }
  temporalTargetPolicy := some { format := "yyyy-MM-dd'T'HH:mm:ss" }
}
private def target := timeField 3 "SelectedClock" ["Projects", "Tasks"] [10, 30]
private def wrongFormatTarget := timeField 4 "WrongClock"
  ["Projects", "Tasks"] [10, 30] "yyyy-MM-dd"
private def fixedTarget := timeField 5 "FixedClock" ["Summary"] []
private def unrelated := timeField 6 "UnrelatedClock" ["Summary"] []

private def model : FlatModel := {
  fields := [source, dateTimeSource, target, wrongFormatTarget, fixedTarget,
    unrelated]
  repeatableGroups := [
    { level := 10, path := ["Projects"], repeatability := some 4 },
    { level := 20, path := ["Projects", "Choices"], repeatability := some 3 },
    { level := 30, path := ["Projects", "Tasks"], repeatability := some 3 }]
}

private def siblingStar (field : String) : SurfaceStarFieldPath := {
  base := .relative 1
  groups := [{ name := "Choices", starred := true }]
  field
}

private def targetStar : SurfaceStarFieldPath := {
  base := .relative 1
  groups := [{ name := "Tasks", starred := true }]
  field := target.name
}

private def operation? :
    Option (CheckedAddressedTimeFirstFilledComputation model) :=
  (checkAddressedTimeFirstFilledComputation model
    ["Projects", "Tasks"] target.id (siblingStar source.name)).toOption

private def elabError? (checked : Except
    AddressedTimeFirstFilledComputationElabError
    (CheckedAddressedTimeFirstFilledComputation model)) :=
  match checked with
  | .error cause => some cause
  | .ok _ => none

/- The checked boundary admits only a repeatable whole-second Time target and one sibling Time star, and it rejects a target read through the reopened axis. -/
example : operation?.isSome = true ∧
    elabError? (checkAddressedTimeFirstFilledComputation model
      ["Projects", "Tasks"] target.id
      (siblingStar dateTimeSource.name)) =
        some (.sourceCarrier dateTimeSource.path) ∧
    elabError? (checkAddressedTimeFirstFilledComputation model
      ["Projects", "Tasks"] wrongFormatTarget.id
      (siblingStar source.name)) =
        some (.targetPolicy (.unsupportedFormat wrongFormatTarget.id
          "yyyy-MM-dd")) ∧
    elabError? (checkAddressedTimeFirstFilledComputation model
      ["Summary"] fixedTarget.id (siblingStar source.name)) =
        some (.targetNotRepeatable fixedTarget.path) ∧
    elabError? (checkAddressedTimeFirstFilledComputation model
      ["Projects", "Tasks"] target.id targetStar) =
        some (.targetSelfReference target.id) := by
  native_decide

private def prepared :
    PreparedFlatStringContext model builtinStringPatternCompiler :=
  (prepareFlatStringContext { now := { epochMillis := 0 } }
    builtinStringPatternCompiler model).toOption.get (by native_decide)

private def clock (hour minute second : Nat)
    (valid : hour < 24 ∧ minute < 60 ∧ second < 60) : TimeOfDay :=
  ⟨hour, minute, second, valid⟩

private def timeValue (epochMillis : Int) (value : TimeOfDay) : RawCell :=
  .parsed (.temporal (.time { epochMillis } value))

private def selectedClock := clock 10 11 12 (by decide)
private def laterClock := clock 13 14 15 (by decide)
private def seedClock := clock 12 34 56 (by decide)
private def unrelatedClock := clock 6 0 0 (by decide)

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
  cell source.id [1, 2] "01:02:03" (timeValue 0 selectedClock),
  cell source.id [2, 1] "13:14:15" (timeValue 47655000 laterClock),
  cell source.id [4, 1] "bad" (.rejected .dateFormat),
  cell source.id [4, 2] "16:17:18"
    (timeValue 58638000 (clock 16 17 18 (by decide))),
  cell target.id [1, 1] "10:11:12" (timeValue 36672000 selectedClock),
  cell target.id [1, 2] "12:34:56" (timeValue 45296000 seedClock),
  cell target.id [3, 1] "12:34:56" (timeValue 45296000 seedClock),
  cell target.id [4, 1] "12:34:56" (timeValue 45296000 seedClock)]

private def stored (text : String) (nonempty : text ≠ "" := by decide) :
    StoredTime := { text, nonempty }

/- Every physical target row scans only its enclosing project's sibling extent. The selected parsed clock, not stored text or transport instant, reaches target rendering. -/
example : (do
    let operation ← operation?
    let input ← input?
    let outcomes ← operation.execute input |>.toOption
    pure (outcomes.map fun entry => (entry.targetField, entry.outcome))) = some [
      (address target.id [1, 1], .accepted (stored "10:11:12")),
      (address target.id [1, 2], .accepted (stored "10:11:12")),
      (address target.id [2, 1], .accepted (stored "13:14:15")),
      (address target.id [3, 1], .noValue),
      (address target.id [4, 1], .poison .dateFormat)] := by
  native_decide

private structure ResultApplicationSummary where
  values : List (CellAddr × String)
  changes : List (CellAddr × String)
  cleared : List CellAddr
  residual : List FormalCause
  noError : Bool
  row11 : TimeTargetState
  row12 : TimeTargetState
  row21 : TimeTargetState
  row31 : TimeTargetState
  row41 : TimeTargetState
  unrelatedState : TimeTargetState
  deriving Repr, DecidableEq

private def resultApplicationSummary? : Option ResultApplicationSummary := do
  let operation ← operation?
  let input ← input?
  let destination ← document? [
    cell target.id [1, 1] "07:00:00"
      (timeValue 25200000 (clock 7 0 0 (by decide))),
    cell unrelated.id [] "06:00:00"
      (timeValue 21600000 unrelatedClock)]
  let result ← operation.executeResult input [.dateFormat] |>.toOption
  let applied ← result.applyToChecked destination |>.toOption
  pure {
    values := result.time.withoutErrors.map fun item =>
      (item.targetField, item.value.text)
    changes := result.time.withChanges.map fun item =>
      (item.targetField, item.value.text)
    cleared := result.time.cleared
    residual := result.time.formalErrorsInOperands
    noError := result.time.noErrorOccurred
    row11 := applied (address target.id [1, 1])
    row12 := applied (address target.id [1, 2])
    row21 := applied (address target.id [2, 1])
    row31 := applied (address target.id [3, 1])
    row41 := applied (address target.id [4, 1])
    unrelatedState := applied (address unrelated.id [])
  }

/- Time retains every accepted result as a changed action, including source-identical input, while clean exhaustion and poison clear only source-filled exact targets in a separate destination. -/
example : resultApplicationSummary? = some {
    values := [
      (address target.id [1, 1], "10:11:12"),
      (address target.id [1, 2], "10:11:12"),
      (address target.id [2, 1], "13:14:15")]
    changes := [
      (address target.id [1, 1], "10:11:12"),
      (address target.id [1, 2], "10:11:12"),
      (address target.id [2, 1], "13:14:15")]
    cleared := [address target.id [3, 1], address target.id [4, 1]]
    residual := [.dateFormat]
    noError := false
    row11 := .presentValue (stored "10:11:12")
    row12 := .presentValue (stored "10:11:12")
    row21 := .presentValue (stored "13:14:15")
    row31 := .presentEmpty
    row41 := .presentEmpty
    unrelatedState := .presentValue (stored "06:00:00")
  } := by
  native_decide

end A12Kernel.Conformance.AddressedTimeFirstFilledComputation
