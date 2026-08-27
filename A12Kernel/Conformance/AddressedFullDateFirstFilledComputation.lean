import A12Kernel.Elaboration.AddressedFullDateFirstFilledComputation

/-! # Exact-address repeatable full-Date `FirstFilledValue` locks -/

namespace A12Kernel.Conformance.AddressedFullDateFirstFilledComputation

open A12Kernel

private def dateField (id : FieldId) (name : String)
    (groupPath : GroupPath) (scope : List RepeatableLevel)
    (format : String := "yyyy-MM-dd")
    (partialMode : TemporalPartialMode := .full)
    (youngerThan1900Check : Bool := false) : FlatFieldDecl := {
  id, name, groupPath, repeatableScope := scope
  policy := { kind := .temporal .date TemporalComponents.fullDate }
  temporalTargetPolicy := some { format, partialMode, youngerThan1900Check }
}

private def source := dateField 1 "PromiseDate"
  ["Projects", "Choices"] [10, 20]
private def dottedSource := dateField 2 "DottedDate"
  ["Projects", "Choices"] [10, 20] "dd.MM.yyyy"
private def timeSource : FlatFieldDecl := {
  id := 3, name := "Clock", groupPath := ["Projects", "Choices"]
  repeatableScope := [10, 20]
  policy := { kind := .temporal .time TemporalComponents.time }
  temporalTargetPolicy := some { format := "HH:mm:ss" }
}
private def target := dateField 4 "SelectedDate"
  ["Projects", "Tasks"] [10, 30] "yyyy-MM-dd" .full true
private def dottedTarget := dateField 5 "DottedTarget"
  ["Projects", "Tasks"] [10, 30] "dd.MM.yyyy"
private def checkedSource := dateField 6 "CheckedSource"
  ["Projects", "Choices"] [10, 20] "yyyy-MM-dd" .full true
private def fixedTarget := dateField 7 "FixedDate" ["Summary"] []
private def unrelated := dateField 8 "UnrelatedDate" ["Summary"] []

private def model : FlatModel := {
  fields := [source, dottedSource, timeSource, target, dottedTarget,
    checkedSource, fixedTarget, unrelated]
  repeatableGroups := [
    { level := 10, path := ["Projects"], repeatability := some 5 },
    { level := 20, path := ["Projects", "Choices"], repeatability := some 3 },
    { level := 30, path := ["Projects", "Tasks"], repeatability := some 3 }]
  timeZoneId := "UTC"
}

private def siblingStar (field : String) : SurfaceStarFieldPath := {
  base := .relative 1
  groups := [{ name := "Choices", starred := true }]
  field
}

private def operation? : Option
    (CheckedAddressedFullDateFirstFilledComputation model) :=
  (checkAddressedFullDateFirstFilledComputation model
    ["Projects", "Tasks"] target.id (siblingStar source.name)).toOption

private def elabError? (checked : Except
    AddressedFullDateFirstFilledComputationElabError
    (CheckedAddressedFullDateFirstFilledComputation model)) :=
  match checked with
  | .error cause => some cause
  | .ok _ => none

/- The checked boundary admits both same-format FULL Date carriers and a checked target, while rejecting crossed, wrong-family, checked-source, and fixed shapes. -/
example : operation?.isSome = true ∧
    (checkAddressedFullDateFirstFilledComputation model
      ["Projects", "Tasks"] dottedTarget.id
      (siblingStar dottedSource.name)).toOption.isSome = true ∧
    elabError? (checkAddressedFullDateFirstFilledComputation model
      ["Projects", "Tasks"] target.id
      (siblingStar dottedSource.name)) =
        some (.sourceCarrier dottedSource.path) ∧
    elabError? (checkAddressedFullDateFirstFilledComputation model
      ["Projects", "Tasks"] target.id (siblingStar timeSource.name)) =
        some (.sourceCarrier timeSource.path) ∧
    elabError? (checkAddressedFullDateFirstFilledComputation model
      ["Projects", "Tasks"] target.id (siblingStar checkedSource.name)) =
        some (.sourceCarrier checkedSource.path) ∧
    elabError? (checkAddressedFullDateFirstFilledComputation model
      ["Summary"] fixedTarget.id (siblingStar source.name)) =
        some (.targetNotRepeatable fixedTarget.path) := by
  native_decide

private def prepared :
    PreparedFlatStringContext model builtinStringPatternCompiler :=
  (prepareFlatStringContext { now := { epochMillis := 0 } }
    builtinStringPatternCompiler model).toOption.get (by native_decide)

private def dateValue (epochMillis year : Int) (month day : Nat) : Value :=
  .temporal (.date {
    instant := { epochMillis }
    parts := { year, month, day }
    basis := .storedGregorian
  })

private def rows : List RowAddr := [
  { group := 10, path := [1] }, { group := 10, path := [2] },
  { group := 10, path := [3] }, { group := 10, path := [4] },
  { group := 10, path := [5] },
  { group := 20, path := [1, 1] }, { group := 20, path := [1, 2] },
  { group := 20, path := [2, 1] }, { group := 20, path := [4, 1] },
  { group := 20, path := [5, 1] },
  { group := 30, path := [1, 1] }, { group := 30, path := [1, 2] },
  { group := 30, path := [2, 1] }, { group := 30, path := [3, 1] },
  { group := 30, path := [4, 1] }, { group := 30, path := [5, 1] },
  { group := 30, path := [5, 2] }]

private def address (field : FieldId) (path : List Nat) : CellAddr :=
  { field, path }

private def cell (field : FieldId) (path : List Nat) (stored : String)
    (raw : RawCell) : ClassifiedCellInput := {
  address := address field path, stored, raw
}

private def document? (cells : List ClassifiedCellInput) :
    Option (CheckedDocument model) :=
  (checkDocument prepared "en_US" { instantiatedRows := rows, cells }).toOption

private def input? : Option (CheckedDocument model) := document? [
  cell source.id [1, 2] "2024-06-15"
    (.parsed (dateValue 1718409600000 2024 6 15)),
  cell source.id [2, 1] "2024-07-16"
    (.parsed (dateValue 1721088000000 2024 7 16)),
  cell source.id [4, 1] "bad" (.rejected .dateFormat),
  cell source.id [5, 1] "1899-12-31"
    (.parsed (dateValue (-2209075200000) 1899 12 31)),
  cell target.id [1, 1] "2024-06-15"
    (.parsed (dateValue 1718409600000 2024 6 15)),
  cell target.id [1, 2] "2024-01-01"
    (.parsed (dateValue 1704067200000 2024 1 1)),
  cell target.id [3, 1] "2024-01-01"
    (.parsed (dateValue 1704067200000 2024 1 1)),
  cell target.id [4, 1] "2024-01-01"
    (.parsed (dateValue 1704067200000 2024 1 1))]

private def stored (text : String) (nonempty : text ≠ "" := by decide) :
    StoredDate := { text, nonempty }

/- Every target row scans its own parent's sibling extent, and target rejection stays distinct from source poison. -/
example : (do
    let operation ← operation?
    let input ← input?
    let outcomes ← operation.execute input |>.toOption
    pure (outcomes.map fun entry => (entry.targetField, entry.outcome))) = some [
      (address target.id [1, 1], .accepted (stored "2024-06-15")),
      (address target.id [1, 2], .accepted (stored "2024-06-15")),
      (address target.id [2, 1], .accepted (stored "2024-07-16")),
      (address target.id [3, 1], .noValue),
      (address target.id [4, 1], .poison .dateFormat),
      (address target.id [5, 1],
        .errored (stored "1899-12-31") .before1900),
      (address target.id [5, 2],
        .errored (stored "1899-12-31") .before1900)] := by
  native_decide

private structure ResultApplicationSummary where
  values : List (CellAddr × String)
  changes : List (CellAddr × String)
  errors : List (CellAddr × String × FullDateTargetError)
  cleared : List CellAddr
  residual : List FormalCause
  row11 : FullDateTargetState
  row12 : FullDateTargetState
  row21 : FullDateTargetState
  row31 : FullDateTargetState
  row41 : FullDateTargetState
  row51 : FullDateTargetState
  row52 : FullDateTargetState
  unrelatedState : FullDateTargetState
  deriving Repr, DecidableEq

private def resultApplicationSummary? : Option ResultApplicationSummary := do
  let operation ← operation?
  let input ← input?
  let destination ← document? [
    cell target.id [1, 1] "2024-01-01"
      (.parsed (dateValue 1704067200000 2024 1 1)),
    cell target.id [5, 1] "2024-01-01"
      (.parsed (dateValue 1704067200000 2024 1 1)),
    cell unrelated.id [] "2024-04-01"
      (.parsed (dateValue 1711929600000 2024 4 1))]
  let result ← operation.executeResult input [.malformed] |>.toOption
  let applied ← result.applyToChecked destination |>.toOption
  pure {
    values := result.fullDate.withoutErrors.map fun item =>
      (item.targetField, item.value.text)
    changes := result.fullDate.withChanges.map fun item =>
      (item.targetField, item.value.text)
    errors := result.fullDate.withErrors.map fun item =>
      (item.targetField, item.attempted.text, item.cause)
    cleared := result.fullDate.cleared
    residual := result.fullDate.formalErrorsInOperands
    row11 := applied (address target.id [1, 1])
    row12 := applied (address target.id [1, 2])
    row21 := applied (address target.id [2, 1])
    row31 := applied (address target.id [3, 1])
    row41 := applied (address target.id [4, 1])
    row51 := applied (address target.id [5, 1])
    row52 := applied (address target.id [5, 2])
    unrelatedState := applied (address unrelated.id [])
  }

/- Result projection keeps exact errors and clears separate; application clears an existing errored destination but does not create an absent one. -/
example : resultApplicationSummary? = some {
    values := [
      (address target.id [1, 1], "2024-06-15"),
      (address target.id [1, 2], "2024-06-15"),
      (address target.id [2, 1], "2024-07-16")]
    changes := [
      (address target.id [1, 2], "2024-06-15"),
      (address target.id [2, 1], "2024-07-16")]
    errors := [
      (address target.id [5, 1], "1899-12-31", .before1900),
      (address target.id [5, 2], "1899-12-31", .before1900)]
    cleared := [address target.id [3, 1], address target.id [4, 1]]
    residual := [.malformed]
    row11 := .presentValue (stored "2024-01-01")
    row12 := .presentValue (stored "2024-06-15")
    row21 := .presentValue (stored "2024-07-16")
    row31 := .presentEmpty
    row41 := .presentEmpty
    row51 := .presentEmpty
    row52 := .absent
    unrelatedState := .presentValue (stored "2024-04-01")
  } := by
  native_decide

end A12Kernel.Conformance.AddressedFullDateFirstFilledComputation
