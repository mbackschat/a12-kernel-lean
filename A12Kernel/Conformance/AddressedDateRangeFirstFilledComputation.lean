import A12Kernel.Elaboration.AddressedDateRangeFirstFilledFormalInput

/-! # Exact-address repeatable DateRange `FirstFilledValue` locks -/

namespace A12Kernel.Conformance.AddressedDateRangeFirstFilledComputation

open A12Kernel

private def rangeField (id : FieldId) (name : String)
    (groupPath : GroupPath) (scope : List RepeatableLevel)
    (format : String := "yyyy-MM-dd") (separator : String := "/") :
    FlatFieldDecl := {
  id, name, groupPath, repeatableScope := scope
  policy := { kind := .dateRange }
  dateRangePolicy := some { format, separator }
}

private def source := rangeField 1 "Window"
  ["Projects", "Choices"] [10, 20]
private def dottedSource := rangeField 2 "DottedWindow"
  ["Projects", "Choices"] [10, 20] "dd.MM.yyyy" "-"
private def monthSource := rangeField 3 "MonthWindow"
  ["Projects", "Choices"] [10, 20] "MM" "/"
private def target := rangeField 4 "SelectedWindow"
  ["Projects", "Tasks"] [10, 30]
private def fixedTarget := rangeField 5 "FixedWindow" ["Summary"] []
private def unrelated := rangeField 6 "UnrelatedWindow" ["Summary"] []

private def model : FlatModel := {
  fields := [source, dottedSource, monthSource, target, fixedTarget, unrelated]
  repeatableGroups := [
    { level := 10, path := ["Projects"], repeatability := some 4 },
    { level := 20, path := ["Projects", "Choices"], repeatability := some 3,
      indexField := some source.id },
    { level := 30, path := ["Projects", "Tasks"], repeatability := some 3 }]
  timeZoneId := "UTC"
}

private def siblingStar (field : String) : SurfaceStarFieldPath := {
  base := .relative 1
  groups := [{ name := "Choices", starred := true }]
  field
}

private def operation? :
    Option (CheckedAddressedDateRangeFirstFilledComputation model) :=
  (checkAddressedDateRangeFirstFilledComputation model
    ["Projects", "Tasks"] target.id (siblingStar source.name)).toOption

private def elabError? (checked : Except
    AddressedDateRangeFirstFilledComputationElabError
    (CheckedAddressedDateRangeFirstFilledComputation model)) :=
  match checked with
  | .error cause => some cause
  | .ok _ => none

/- The checked boundary accepts component-equivalent DateRange spellings, refuses a different component set, and requires a repeatable target. -/
example : operation?.isSome = true ∧
    (checkAddressedDateRangeFirstFilledComputation model
      ["Projects", "Tasks"] target.id
      (siblingStar dottedSource.name)).toOption.isSome = true ∧
    elabError? (checkAddressedDateRangeFirstFilledComputation model
      ["Projects", "Tasks"] target.id
      (siblingStar monthSource.name)) =
        some (.sourceProfileNotComparable target.path monthSource.path) ∧
    elabError? (checkAddressedDateRangeFirstFilledComputation model
      ["Summary"] fixedTarget.id (siblingStar source.name)) =
        some (.targetNotRepeatable fixedTarget.path) := by
  native_decide

private def prepared :
    PreparedFlatStringContext model builtinStringPatternCompiler :=
  (prepareFlatStringContext { now := { epochMillis := 0 } }
    builtinStringPatternCompiler model).toOption.get (by native_decide)

private def dateValue (epochMillis : Int) (month day : Nat) : DateValue := {
  instant := { epochMillis }
  parts := { year := 2024, month, day }
  basis := .storedGregorian
}

private def rangeValue (startMillis finishMillis : Int)
    (startMonth startDay finishMonth finishDay : Nat) : DateRangeValue := {
  start := dateValue startMillis startMonth startDay
  finish := dateValue finishMillis finishMonth finishDay
}

private def june := rangeValue 1717200000000 1719705600000 6 1 6 30
private def july := rangeValue 1719792000000 1722384000000 7 1 7 31
private def seed := rangeValue 1704067200000 1704153600000 1 1 1 2

private def rows : List RowAddr := [
  { group := 10, path := [1] }, { group := 10, path := [2] },
  { group := 10, path := [3] }, { group := 10, path := [4] },
  { group := 20, path := [1, 1] }, { group := 20, path := [1, 2] },
  { group := 20, path := [2, 1] }, { group := 20, path := [4, 1] },
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
  cell source.id [1, 1] "2024-06-01/2024-06-30"
    (.parsed (.dateRange june)),
  cell source.id [1, 2] "2024-06-01/2024-06-30"
    (.parsed (.dateRange june)),
  cell source.id [2, 1] "2024-07-01/2024-07-31"
    (.parsed (.dateRange july)),
  cell source.id [4, 1] "bad" (.rejected .dateRangeSeparator),
  cell target.id [1, 1] "2024-06-01/2024-06-30"
    (.parsed (.dateRange june)),
  cell target.id [1, 2] "2024-01-01/2024-01-02"
    (.parsed (.dateRange seed)),
  cell target.id [3, 1] "2024-01-01/2024-01-02"
    (.parsed (.dateRange seed)),
  cell target.id [4, 1] "2024-01-01/2024-01-02"
    (.parsed (.dateRange seed))]

private def stored (text : String) (nonempty : text ≠ "" := by decide) :
    StoredDateRange := { text, nonempty }

/- Each physical target row scans only its enclosing project's sibling source extent and retains its exact target address. -/
example : (do
    let operation ← operation?
    let input ← input?
    let outcomes ← operation.execute input |>.toOption
    pure (outcomes.map fun entry => (entry.targetField, entry.outcome))) = some [
      (address target.id [1, 1], .accepted (stored "2024-06-01/2024-06-30")),
      (address target.id [1, 2], .accepted (stored "2024-06-01/2024-06-30")),
      (address target.id [2, 1], .accepted (stored "2024-07-01/2024-07-31")),
      (address target.id [3, 1], .noValue),
      (address target.id [4, 1], .poison .dateRangeSeparator)] := by
  native_decide

/- The whole-call route selects one preliminary for the source declaration: both duplicate DateRange index cells remain in the eager inventory and poison each reached first-project scan, while other parents preserve their ordinary outcomes. -/
example : (do
    let operation ← operation?
    let input ← input?
    let result ← operation.executeResultWithFormalInputs input |>.toOption
    pure (
      result.dateRange.formalErrorsInOperands,
      result.dateRange.withoutErrors.map (·.targetField),
      result.dateRange.withErrors.map (·.targetField),
      result.dateRange.cleared)) = some ([
        {
          address := address source.id [4, 1]
          cause := .dateRangeSeparator
        },
        {
          address := address source.id [1, 1]
          cause := .duplicateIndex
        },
        {
          address := address source.id [1, 2]
          cause := .duplicateIndex
        }
      ], [address target.id [2, 1]], [], [
        address target.id [1, 1],
        address target.id [1, 2],
        address target.id [3, 1],
        address target.id [4, 1]
      ]) := by
  native_decide

private def duplicateFirstChoiceRead (input : CheckedDocument model)
    (exact : CellAddr) : Except CheckedDocumentError CheckedCell := do
  let base ← input.read exact
  if exact = address source.id [1, 1] then
    pure (base.withFinding .duplicateIndex)
  else
    pure base

/- A caller-supplied exact-address view changes only the reached leaf observations: immutable sibling topology and target-row placement stay unchanged, while an earlier poisoned empty source terminates the first project's scan before its later value. -/
example : (do
    let operation ← operation?
    let input ← input?
    let outcomes ← operation.executeWithRead input
      (duplicateFirstChoiceRead input) |>.toOption
    pure (outcomes.map fun entry => (entry.targetField, entry.outcome))) = some [
      (address target.id [1, 1], .poison .duplicateIndex),
      (address target.id [1, 2], .poison .duplicateIndex),
      (address target.id [2, 1], .accepted (stored "2024-07-01/2024-07-31")),
      (address target.id [3, 1], .noValue),
      (address target.id [4, 1], .poison .dateRangeSeparator)] := by
  native_decide

private def addressedErrorView : DateRangeComputationRunView String CellAddr :=
  DateRangeComputationRunView.fromOutcomesAt (fun _ => .absent) ["residual"] [
    (address target.id [2, 1],
      .errored (stored "2024-07-31/2024-07-01") .inverted)]

private def addressedError : DateRangeComputedError CellAddr := {
  targetField := address target.id [2, 1]
  attempted := stored "2024-07-31/2024-07-01"
  cause := .inverted
}

/- Exact target identity survives the DateRange error projection, independently of the supplied residual channel. -/
example : (addressedErrorView.withErrors,
    addressedErrorView.formalErrorsInOperands) =
    ([addressedError], ["residual"]) := by
  native_decide

private structure ResultApplicationSummary where
  values : List (CellAddr × String)
  changes : List (CellAddr × String)
  cleared : List CellAddr
  row11 : TemporalTargetState StoredDateRange
  row12 : TemporalTargetState StoredDateRange
  row21 : TemporalTargetState StoredDateRange
  row31 : TemporalTargetState StoredDateRange
  row41 : TemporalTargetState StoredDateRange
  unrelatedState : TemporalTargetState StoredDateRange
  deriving Repr, DecidableEq

private def resultApplicationSummary? : Option ResultApplicationSummary := do
  let operation ← operation?
  let input ← input?
  let destination ← document? [
    cell target.id [1, 1] "2024-01-01/2024-01-02"
      (.parsed (.dateRange seed)),
    cell unrelated.id [] "2024-01-01/2024-01-02"
      (.parsed (.dateRange seed))]
  let result ← operation.executeResult input ([] : List FormalCause) |>.toOption
  let applied ← result.applyToChecked destination |>.toOption
  pure {
    values := result.dateRange.withoutErrors.map fun item =>
      (item.targetField, item.value.text)
    changes := result.dateRange.withChanges.map fun item =>
      (item.targetField, item.value.text)
    cleared := result.dateRange.cleared
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
      (address target.id [1, 1], "2024-06-01/2024-06-30"),
      (address target.id [1, 2], "2024-06-01/2024-06-30"),
      (address target.id [2, 1], "2024-07-01/2024-07-31")]
    changes := [
      (address target.id [1, 2], "2024-06-01/2024-06-30"),
      (address target.id [2, 1], "2024-07-01/2024-07-31")]
    cleared := [address target.id [3, 1], address target.id [4, 1]]
    row11 := .presentValue (stored "2024-01-01/2024-01-02")
    row12 := .presentValue (stored "2024-06-01/2024-06-30")
    row21 := .presentValue (stored "2024-07-01/2024-07-31")
    row31 := .presentEmpty
    row41 := .presentEmpty
    unrelatedState := .presentValue (stored "2024-01-01/2024-01-02")
  } := by
  native_decide

end A12Kernel.Conformance.AddressedDateRangeFirstFilledComputation
