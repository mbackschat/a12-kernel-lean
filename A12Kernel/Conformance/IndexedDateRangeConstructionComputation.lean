import A12Kernel.Elaboration.IndexedDateRangeConstructionComputation

/-! # Literal-keyed DateRange construction computation locks -/

namespace A12Kernel.Conformance.IndexedDateRangeConstructionComputation

open A12Kernel

private def index : FlatFieldDecl := {
  id := 1
  groupPath := ["Order", "Items"]
  name := "Sku"
  policy := { kind := .string }
  repeatableScope := [10]
}

private def dateField (id : FieldId) (name : String) : FlatFieldDecl := {
  id
  groupPath := ["Order", "Items"]
  name
  policy := { kind := .temporal .date TemporalComponents.fullDate }
  temporalTargetPolicy := some { format := "yyyy-MM-dd", partialMode := .full }
  repeatableScope := [10]
}

private def start := dateField 2 "PromiseStart"
private def finish := dateField 3 "PromiseFinish"
private def target : FlatFieldDecl := {
  id := 4
  groupPath := ["Order"]
  name := "Coverage"
  policy := { kind := .dateRange }
  dateRangePolicy := some { format := "yyyy-MM-dd", separator := "/" }
}

private def items : RepeatableGroupDecl := {
  level := 10
  path := ["Order", "Items"]
  repeatability := some 20
  indexField := some index.id
}

private def model : FlatModel := {
  fields := [index, start, finish, target]
  repeatableGroups := [items]
  timeZoneId := "UTC"
}

private def row (coordinate : Nat) : RowAddr := { group := 10, path := [coordinate] }

private def dateValue (year : Int) (month day : Nat) : DateValue := {
  instant := { epochMillis := 0 }
  parts := { year, month, day }
  basis := .storedGregorian
}

private def cell (field coordinate : Nat) (stored : String) (raw : RawCell) :
    ClassifiedCellInput := {
  address := { field, path := [coordinate] }
  stored
  raw
}

private def data (duplicate emptyStart : Bool) : DocumentData := {
  instantiatedRows := [row 1, row 2]
  cells := [
    cell index.id 1 "sku1" (.parsed (.str "sku1")),
    cell start.id 1 (if emptyStart then "" else "2024-01-01")
      (if emptyStart then .presentEmpty else .parsed (.temporal (.date (dateValue 2024 1 1)))),
    cell finish.id 1 "2024-01-31" (.parsed (.temporal (.date (dateValue 2024 1 31)))),
    cell index.id 2 (if duplicate then "sku1" else "sku2")
      (.parsed (.str (if duplicate then "sku1" else "sku2"))),
    cell start.id 2 "2024-02-01" (.parsed (.temporal (.date (dateValue 2024 2 1)))),
    cell finish.id 2 "2024-02-29" (.parsed (.temporal (.date (dateValue 2024 2 29))))
  ]
}

private def preliminary? (source : DocumentData) : Option (CheckedIndexPreliminary model) := do
  let prepared ← (prepareFlatStringContext { now := { epochMillis := 0 } }
    builtinStringPatternCompiler model).toOption
  let checked ← (checkDocument prepared "en_US" source).toOption
  checked.applyFullIndexPreliminary.toOption

private def operation? (startKey finishKey : String) :=
  (elaborateIndexedDateRangeConstructionComputation model ["Order"] target.id
    start.id startKey finish.id finishKey).toOption

private def execute? (startKey finishKey : String) (source : DocumentData) := do
  let operation ← operation? startKey finishKey
  let preliminary ← preliminary? source
  (operation.execute preliminary).toOption

private def expected : StoredDateRange := {
  text := "2024-01-01/2024-02-29"
  nonempty := by decide
}

/- Exact literal keys may select different rows; the rich result retains both concrete addresses. -/
example : (execute? "sku1" "sku2" (data false false)).map (fun result =>
    (result.start.address, result.finish.address, result.outcome)) =
  some (some { field := start.id, path := [1] },
    some { field := finish.id, path := [2] }, .accepted expected) := by
  native_decide

/- Reversing only the keys reverses the selected endpoint rows rather than falling back to physical order. -/
example : (execute? "sku2" "sku1" (data false false)).map (fun result =>
    (result.start.address, result.finish.address)) =
  some (some { field := start.id, path := [2] },
    some { field := finish.id, path := [1] }) := by
  native_decide

/- A clean missing key has no selected address, while a selected empty endpoint retains its row address; both clear without a formal cause. -/
example :
    (execute? "missing" "sku2" (data false false)).map (fun result =>
        (result.start.address, result.start.value, result.outcome)) =
        some (none, .empty, .noValue) ∧
      (execute? "sku1" "sku2" (data false true)).map (fun result =>
        (result.start.address, result.start.value, result.outcome)) =
        some (some { field := start.id, path := [1] }, .empty, .noValue) := by
  native_decide

/- Duplicate index participants poison computation before lookup, expose no selected address, and clear an existing target. -/
example : (execute? "sku1" "sku1" (data true false)).map (fun result =>
    (result.start.address, result.finish.address, result.outcome,
      result.outcome.applyTo (.presentValue expected))) =
  some (none, none, .poison .duplicateIndex, .presentEmpty) := by
  native_decide

/- This first checked profile refuses partial Date components, a non-String index, nested repeatable scope, and endpoints from different indexed groups. -/
example :
    let partialComponents :=
      { TemporalComponents.fullDate with day := false }
    let partialStart := { start with
      policy := { kind := .temporal .date partialComponents } }
    let partialModel := { model with fields := [index, partialStart, finish, target] }
    let numberIndex := { index with
      policy := { kind := .number { scale := 0, signed := false } } }
    let numberModel := { model with fields := [numberIndex, start, finish, target] }
    let outer : RepeatableGroupDecl := { level := 5, path := ["Order", "Sections"] }
    let nestedItems := { items with path := ["Order", "Sections", "Items"] }
    let nestedStart := { start with groupPath := nestedItems.path, repeatableScope := [5, 10] }
    let nestedFinish := { finish with groupPath := nestedItems.path, repeatableScope := [5, 10] }
    let nestedIndex := { index with groupPath := nestedItems.path, repeatableScope := [5, 10] }
    let nestedModel : FlatModel := { model with
      fields := [nestedIndex, nestedStart, nestedFinish, target]
      repeatableGroups := [outer, nestedItems] }
    let otherIndex := { index with id := 5, groupPath := ["Order", "Other"], repeatableScope := [20] }
    let otherFinish := { finish with id := 6, groupPath := ["Order", "Other"], repeatableScope := [20] }
    let other : RepeatableGroupDecl := {
      level := 20, path := ["Order", "Other"], indexField := some otherIndex.id }
    let crossModel : FlatModel := { model with
      fields := [index, start, otherIndex, otherFinish, target]
      repeatableGroups := [items, other] }
    (elaborateIndexedDateRangeConstructionComputation partialModel ["Order"] target.id
      partialStart.id "sku1" finish.id "sku2").isOk = false ∧
    (elaborateIndexedDateRangeConstructionComputation numberModel ["Order"] target.id
      start.id "sku1" finish.id "sku2").isOk = false ∧
    (elaborateIndexedDateRangeConstructionComputation nestedModel ["Order"] target.id
      nestedStart.id "sku1" nestedFinish.id "sku2").isOk = false ∧
    (elaborateIndexedDateRangeConstructionComputation crossModel ["Order"] target.id
      start.id "sku1" otherFinish.id "sku2").isOk = false := by
  native_decide

end A12Kernel.Conformance.IndexedDateRangeConstructionComputation
