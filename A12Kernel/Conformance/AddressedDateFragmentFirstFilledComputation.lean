import A12Kernel.Elaboration.AddressedDateFragmentFirstFilledComputation

/-! # Exact-address repeatable DateFragment `FirstFilledValue` locks -/

namespace A12Kernel.Conformance.AddressedDateFragmentFirstFilledComputation

open A12Kernel

private def fragmentField (id : FieldId) (name : String)
    (groupPath : GroupPath) (scope : List RepeatableLevel)
    (format : String := "MM") : FlatFieldDecl := {
  id, name, groupPath, repeatableScope := scope
  policy := { kind := .temporal .date TemporalComponents.fullDate }
  temporalTargetPolicy := some {
    format
    partialMode := .yearOptional
  }
}

private def source := fragmentField 1 "Month"
  ["Projects", "Choices"] [10, 20]
private def target := fragmentField 2 "SelectedMonth"
  ["Projects", "Tasks"] [10, 30]
private def yearSource := fragmentField 3 "Year"
  ["Projects", "Choices"] [10, 20] "yyyy"
private def yearTarget := fragmentField 4 "SelectedYear"
  ["Projects", "Tasks"] [10, 30] "yyyy"
private def yearMonthSource := fragmentField 5 "YearMonth"
  ["Projects", "Choices"] [10, 20] "yyyy-MM"
private def yearMonthTarget := fragmentField 6 "SelectedYearMonth"
  ["Projects", "Tasks"] [10, 30] "yyyy-MM"
private def monthDaySource := fragmentField 7 "MonthDay"
  ["Projects", "Choices"] [10, 20] "MM-dd"
private def monthDayTarget := fragmentField 8 "SelectedMonthDay"
  ["Projects", "Tasks"] [10, 30] "MM-dd"
private def fixedTarget := fragmentField 9 "FixedMonth" ["Summary"] []
private def unrelated := fragmentField 10 "UnrelatedMonth" ["Summary"] []

private def fullDateTarget : FlatFieldDecl := {
  id := 11
  name := "FullDate"
  groupPath := ["Projects", "Tasks"]
  repeatableScope := [10, 30]
  policy := { kind := .temporal .date TemporalComponents.fullDate }
  temporalTargetPolicy := some { format := "yyyy-MM-dd" }
}

private def model : FlatModel := {
  fields := [source, target, yearSource, yearTarget, yearMonthSource,
    yearMonthTarget, monthDaySource, monthDayTarget, fixedTarget, unrelated,
    fullDateTarget]
  repeatableGroups := [
    { level := 10, path := ["Projects"], repeatability := some 3 },
    { level := 20, path := ["Projects", "Choices"], repeatability := some 2 },
    { level := 30, path := ["Projects", "Tasks"], repeatability := some 2 }]
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
    Option (CheckedAddressedDateFragmentFirstFilledComputation model) :=
  (checkAddressedDateFragmentFirstFilledComputation model
    ["Projects", "Tasks"] target.id (siblingStar source.name)).toOption

private def elabError? (checked : Except
    AddressedDateFragmentFirstFilledComputationElabError
    (CheckedAddressedDateFragmentFirstFilledComputation model)) :=
  match checked with
  | .error cause => some cause
  | .ok _ => none

/- The addressed boundary admits all four exact fragment profiles and separates target placement, carrier identity, and self-reference. -/
example : operation?.isSome = true ∧
    (checkAddressedDateFragmentFirstFilledComputation model
      ["Projects", "Tasks"] yearTarget.id
      (siblingStar yearSource.name)).toOption.isSome = true ∧
    (checkAddressedDateFragmentFirstFilledComputation model
      ["Projects", "Tasks"] yearMonthTarget.id
      (siblingStar yearMonthSource.name)).toOption.isSome = true ∧
    (checkAddressedDateFragmentFirstFilledComputation model
      ["Projects", "Tasks"] monthDayTarget.id
      (siblingStar monthDaySource.name)).toOption.isSome = true ∧
    elabError? (checkAddressedDateFragmentFirstFilledComputation model
      ["Projects", "Tasks"] target.id
      (siblingStar yearSource.name)) =
        some (.sourceCarrier yearSource.path .monthFragment
          (some .yearFragment)) ∧
    elabError? (checkAddressedDateFragmentFirstFilledComputation model
      ["Projects", "Tasks"] fullDateTarget.id
      (siblingStar source.name)) =
        some (.targetCarrier fullDateTarget.path) ∧
    elabError? (checkAddressedDateFragmentFirstFilledComputation model
      ["Summary"] fixedTarget.id (siblingStar source.name)) =
        some (.targetNotRepeatable fixedTarget.path) ∧
    elabError? (checkAddressedDateFragmentFirstFilledComputation model
      ["Projects", "Tasks"] target.id targetStar) =
        some (.targetSelfReference target.id) := by
  native_decide

private def prepared :
    PreparedFlatStringContext model builtinStringPatternCompiler :=
  (prepareFlatStringContext { now := { epochMillis := 0 } }
    builtinStringPatternCompiler model).toOption.get (by native_decide)

private def dateValue (month : Nat) : RawCell :=
  .parsed (.temporal (.date {
    instant := { epochMillis := 0 }
    parts := { year := 2000, month, day := 1 }
    basis := .storedGregorian
  }))

private def rows : List RowAddr := [
  { group := 10, path := [1] }, { group := 10, path := [2] },
  { group := 10, path := [3] },
  { group := 20, path := [1, 1] }, { group := 20, path := [1, 2] },
  { group := 20, path := [2, 1] }, { group := 20, path := [2, 2] },
  { group := 30, path := [2, 2] }, { group := 30, path := [1, 1] },
  { group := 30, path := [3, 1] }, { group := 30, path := [2, 1] },
  { group := 30, path := [1, 2] }]

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
  cell source.id [1, 2] "06" (dateValue 6),
  cell source.id [2, 1] "XX" (.rejected .malformed),
  cell source.id [2, 2] "07" (dateValue 7),
  cell target.id [1, 1] "06" (dateValue 6),
  cell target.id [1, 2] "05" (dateValue 5),
  cell target.id [2, 1] "05" (dateValue 5),
  cell target.id [3, 1] "05" (dateValue 5)]

/- Physical target encounter order is preserved, each row scans only its enclosing sibling extent, and DateFragment retains the exact selected stored token. -/
example : (do
    let operation ← operation?
    let input ← input?
    let outcomes ← operation.execute input |>.toOption
    pure (outcomes.map fun entry => (entry.targetField, entry.result))) = some [
      (address target.id [2, 2], .poison .malformed),
      (address target.id [1, 1], .value "06"),
      (address target.id [3, 1], .noValue),
      (address target.id [2, 1], .poison .malformed),
      (address target.id [1, 2], .value "06")] := by
  native_decide

private structure ResultApplicationSummary where
  values : List (CellAddr × String)
  changes : List (CellAddr × String)
  errors : List (CellAddr × String)
  cleared : List CellAddr
  residual : List FormalCause
  row11 : StringTargetState
  row12 : StringTargetState
  row21 : StringTargetState
  row22 : StringTargetState
  row31 : StringTargetState
  unrelatedState : StringTargetState
  deriving Repr, DecidableEq

private def resultApplicationSummary? : Option ResultApplicationSummary := do
  let operation ← operation?
  let input ← input?
  let destination ← document? [
    cell target.id [1, 1] "04" (dateValue 4),
    cell target.id [1, 2] "04" (dateValue 4),
    cell target.id [2, 1] "04" (dateValue 4),
    cell unrelated.id [] "03" (dateValue 3)]
  let result ← operation.executeResult input [.malformed] |>.toOption
  let applied ← result.applyToChecked destination |>.toOption
  pure {
    values := result.string.withoutErrors.map fun item =>
      (item.targetField, item.value.text)
    changes := result.string.withChanges.map fun item =>
      (item.targetField, item.value.text)
    errors := result.string.withErrors.map fun item =>
      (item.targetField, item.attempted.text)
    cleared := result.string.cleared
    residual := result.string.formalErrorsInOperands
    row11 := applied (address target.id [1, 1])
    row12 := applied (address target.id [1, 2])
    row21 := applied (address target.id [2, 1])
    row22 := applied (address target.id [2, 2])
    row31 := applied (address target.id [3, 1])
    unrelatedState := applied (address unrelated.id [])
  }

/- Exact source classification keeps the source-identical token inert, applies the changed sibling, and retains clears only for source-filled targets in a separate destination. -/
example : resultApplicationSummary? = some {
    values := [
      (address target.id [1, 1], "06"),
      (address target.id [1, 2], "06")]
    changes := [(address target.id [1, 2], "06")]
    errors := []
    cleared := [address target.id [3, 1], address target.id [2, 1]]
    residual := [.malformed]
    row11 := .presentValue ⟨"04", by decide⟩
    row12 := .presentValue ⟨"06", by decide⟩
    row21 := .presentEmpty
    row22 := .absent
    row31 := .presentEmpty
    unrelatedState := .presentValue ⟨"03", by decide⟩
  } := by
  native_decide

end A12Kernel.Conformance.AddressedDateFragmentFirstFilledComputation
