import A12Kernel.Elaboration.IndexedDateRangeConstructionComputation
import A12Kernel.Elaboration.TemporalErroredComputationApplication

/-! # String-keyed DateRange construction computation locks -/

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

private def unrelatedTarget : FlatFieldDecl := {
  target with id := 7, name := "UnrelatedCoverage"
}

private def selector (id : FieldId) (name : String) : FlatFieldDecl := {
  id
  groupPath := ["Order"]
  name
  policy := { kind := .string }
}

private def startSelector := selector 5 "StartSelector"
private def finishSelector := selector 6 "FinishSelector"

private def items : RepeatableGroupDecl := {
  level := 10
  path := ["Order", "Items"]
  repeatability := some 20
  indexField := some index.id
}

private def model : FlatModel := {
  fields := [index, start, finish, target, startSelector, finishSelector,
    unrelatedTarget]
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

private def directCell (field : FieldId) (stored : String) (raw : RawCell) :
    ClassifiedCellInput := {
  address := { field, path := [] }
  stored
  raw
}

private def dataWithSelectors (duplicate emptyStart : Bool)
    (startSelectorStored finishSelectorStored : String)
    (startSelectorRaw finishSelectorRaw : RawCell) : DocumentData := {
  instantiatedRows := [row 1, row 2]
  cells := [
    cell index.id 1 "sku1" (.parsed (.str "sku1")),
    cell start.id 1 (if emptyStart then "" else "2024-01-01")
      (if emptyStart then .presentEmpty else .parsed (.temporal (.date (dateValue 2024 1 1)))),
    cell finish.id 1 "2024-01-31" (.parsed (.temporal (.date (dateValue 2024 1 31)))),
    cell index.id 2 (if duplicate then "sku1" else "sku2")
      (.parsed (.str (if duplicate then "sku1" else "sku2"))),
    cell start.id 2 "2024-02-01" (.parsed (.temporal (.date (dateValue 2024 2 1)))),
    cell finish.id 2 "2024-02-29" (.parsed (.temporal (.date (dateValue 2024 2 29)))),
    directCell startSelector.id startSelectorStored startSelectorRaw,
    directCell finishSelector.id finishSelectorStored finishSelectorRaw
  ]
}

private def data (duplicate emptyStart : Bool) : DocumentData :=
  dataWithSelectors duplicate emptyStart "sku1" "sku2"
    (.parsed (.str "sku1")) (.parsed (.str "sku2"))

private def checkedDocument? (source : DocumentData) :
    Option (CheckedDocument model) := do
  let prepared ← (prepareFlatStringContext { now := { epochMillis := 0 } }
    builtinStringPatternCompiler model).toOption
  (checkDocument prepared "en_US" source).toOption

private def preliminary? (source : DocumentData) :
    Option (CheckedIndexPreliminary model) := do
  let checked ← checkedDocument? source
  checked.applyFullIndexPreliminary.toOption

private def operation? (startKey finishKey : String) :=
  (elaborateIndexedDateRangeConstructionComputation model ["Order"] target.id
    start.id startKey finish.id finishKey).toOption

private def execute? (startKey finishKey : String) (source : DocumentData) := do
  let operation ← operation? startKey finishKey
  let preliminary ← preliminary? source
  (operation.execute preliminary).toOption

private def fieldOperation? :=
  (elaborateIndexedDateRangeConstructionComputation model ["Order"] target.id
    start.id (.field startSelector.id) finish.id (.field finishSelector.id)).toOption

private def fieldExecute? (source : DocumentData) := do
  let operation ← fieldOperation?
  let preliminary ← preliminary? source
  (operation.execute preliminary).toOption

private def elaborationErrorOf {checkedModel : FlatModel} :
    Except IndexedDateRangeConstructionComputationElabError
      (CheckedIndexedDateRangeConstructionComputation checkedModel) →
        Option IndexedDateRangeConstructionComputationElabError
  | .ok _ => none
  | .error cause => some cause

private def expected : StoredDateRange := {
  text := "2024-01-01/2024-02-29"
  nonempty := by decide
}

private def exactDateValue (epochMillis : Int) (year : Int)
    (month day : Nat) : DateValue := {
  instant := { epochMillis }
  parts := { year, month, day }
  basis := .storedGregorian
}

private def expectedRange : DateRangeValue := {
  start := exactDateValue 1704067200000 2024 1 1
  finish := exactDateValue 1709164800000 2024 2 29
}

private def priorStored : StoredDateRange := {
  text := "2023-12-01/2023-12-31"
  nonempty := by decide
}

private def priorRange : DateRangeValue := {
  start := exactDateValue 1701388800000 2023 12 1
  finish := exactDateValue 1703980800000 2023 12 31
}

private def unrelatedStored : StoredDateRange := {
  text := "2024-03-01/2024-03-31"
  nonempty := by decide
}

private def invertedStored : StoredDateRange := {
  text := "2024-02-01/2024-01-31"
  nonempty := by decide
}

private def unrelatedRange : DateRangeValue := {
  start := exactDateValue 1709251200000 2024 3 1
  finish := exactDateValue 1711843200000 2024 3 31
}

private def withTarget (source : DocumentData) (stored : StoredDateRange)
    (range : DateRangeValue) : DocumentData := {
  source with cells := source.cells ++
    [directCell target.id stored.text (.parsed (.dateRange range))]
}

private def resultView? (startKey finishKey : String) (source : DocumentData)
    (targetStored : StoredDateRange) (targetRange : DateRangeValue)
    (residualMessages : List FormalCause := []) :
    Option (DateRangeComputationRunView FormalCause) := do
  let operation ← operation? startKey finishKey
  let preliminary ← preliminary? (withTarget source targetStored targetRange)
  operation.executeResult preliminary residualMessages |>.toOption

private def destination? (includeTarget : Bool) :
    Option (CheckedDocument model) :=
  let targetCells := if includeTarget then
    [directCell target.id priorStored.text (.parsed (.dateRange priorRange))]
  else []
  let source := data false false
  checkedDocument? { source with cells := source.cells ++ targetCells ++ [
    directCell unrelatedTarget.id unrelatedStored.text
      (.parsed (.dateRange unrelatedRange))] }

/- Exact literal keys may select different rows; the rich result retains both concrete addresses. -/
example : (execute? "sku1" "sku2" (data false false)).map (fun result =>
    (result.start.key, result.start.address, result.finish.key,
      result.finish.address, result.outcome)) =
  some (.literal "sku1", some { field := start.id, path := [1] },
    .literal "sku2", some { field := finish.id, path := [2] },
    .accepted expected) := by
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

/- Direct evaluated String selector fields retain their checked observations and select the same concrete rows as literal keys. -/
example : (fieldExecute? (data false false)).map (fun result =>
    (result.start.key, result.start.address, result.finish.key,
      result.finish.address, result.outcome)) =
  some (.field { id := startSelector.id } (.value "sku1"),
    some { field := start.id, path := [1] },
    .field { id := finishSelector.id } (.value "sku2"),
    some { field := finish.id, path := [2] }, .accepted expected) := by
  native_decide

/- Changing only the checked selector-field values reverses physical endpoint selection. -/
example : (fieldExecute? (dataWithSelectors false false "sku2" "sku1"
    (.parsed (.str "sku2")) (.parsed (.str "sku1")))).map (fun result =>
      (result.start.address, result.finish.address)) =
  some (some { field := start.id, path := [2] },
    some { field := finish.id, path := [1] }) := by
  native_decide

/- A filled no-match selector and an empty selector retain distinct key observations while both expose no selected address and clear the target. -/
example :
    (fieldExecute? (dataWithSelectors false false "missing" "sku2"
      (.parsed (.str "missing")) (.parsed (.str "sku2")))).map (fun result =>
        (result.start.key, result.start.address, result.outcome)) =
      some (.field { id := startSelector.id } (.value "missing"), none, .noValue) ∧
    (fieldExecute? (dataWithSelectors false false "" "sku2"
      .presentEmpty (.parsed (.str "sku2")))).map (fun result =>
        (result.start.key, result.start.address, result.outcome)) =
      some (.field { id := startSelector.id } .empty, none, .noValue) := by
  native_decide

/- A formally unavailable selector retains its exact computation-phase cause and poisons the endpoint before target assembly. -/
example : (fieldExecute? (dataWithSelectors false false "bad" "sku2"
    (.rejected .declaredConstraint) (.parsed (.str "sku2")))).map (fun result =>
      (result.start.key, result.start.address, result.start.value, result.outcome)) =
  some (.field { id := startSelector.id } (.poison .declaredConstraint),
    none, .poison .declaredConstraint, .poison .declaredConstraint) := by
  native_decide

/- Duplicate index participants poison field-keyed selection before either endpoint exposes an address. -/
example : (fieldExecute? (data true false)).map (fun result =>
    (result.start.key, result.start.address, result.finish.key,
      result.finish.address, result.outcome)) =
  some (.field { id := startSelector.id } (.value "sku1"), none,
    .field { id := finishSelector.id } (.value "sku2"), none,
    .poison .duplicateIndex) := by
  native_decide

/- A raw String selector remains a valid model declaration but not an evaluated field-valued key. -/
example :
    let rawSelector := { startSelector with
      stringValueMode := .raw
      stringPolicy := { lineBreaksPermitted := true } }
    let rawModel := { model with
      fields := [index, start, finish, target, rawSelector, finishSelector] }
    rawModel.validate.isOk = true ∧
    elaborationErrorOf
      (elaborateIndexedDateRangeConstructionComputation rawModel ["Order"] target.id
        start.id (.field rawSelector.id) finish.id (.field finishSelector.id)) =
      some (.start (.keyNotEvaluatedString rawSelector.path)) := by
  native_decide

/- A non-String selector remains model-valid but is refused at exact key-value admission. -/
example :
    let numberSelector := { startSelector with
      policy := { kind := .number { scale := 0, signed := false } } }
    let numberModel := { model with
      fields := [index, start, finish, target, numberSelector, finishSelector] }
    numberModel.validate.isOk = true ∧
    elaborationErrorOf
      (elaborateIndexedDateRangeConstructionComputation numberModel ["Order"] target.id
        start.id (.field numberSelector.id) finish.id (.field finishSelector.id)) =
      some (.start (.keyNotEvaluatedString numberSelector.path)) := by
  native_decide

/- A repeatable String selector remains model-valid but is refused by the direct-key boundary. -/
example :
    let repeatableSelector := { startSelector with
      groupPath := items.path, repeatableScope := [items.level] }
    let repeatableModel := { model with
      fields := [index, start, finish, target, repeatableSelector, finishSelector] }
    repeatableModel.validate.isOk = true ∧
    elaborationErrorOf
      (elaborateIndexedDateRangeConstructionComputation repeatableModel ["Order"] target.id
        start.id (.field repeatableSelector.id) finish.id (.field finishSelector.id)) =
      some (.start (.resolve (.repeatableReference repeatableSelector.path))) := by
  native_decide

/- Duplicate index participants poison computation before lookup, expose no selected address, and clear an existing target. -/
example : (execute? "sku1" "sku1" (data true false)).map (fun result =>
    (result.start.address, result.finish.address, result.outcome,
      result.outcome.applyTo (.presentValue expected))) =
  some (none, none, .poison .duplicateIndex, .presentEmpty) := by
  native_decide

/- Indexed rich execution classifies the direct target against its immutable source, then applies only the retained accepted change to a separate destination. -/
example : (do
    let view ← resultView? "sku1" "sku2" (data false false)
      priorStored priorRange
    let destination ← destination? true
    let applied ← view.applyToChecked destination |>.toOption
    pure ((view.withoutErrors, view.withChanges, view.withErrors),
      (applied target.id, applied unrelatedTarget.id))) =
    some ((([{ targetField := target.id, value := expected }] :
        List DateRangeComputedInstance),
      ([{ targetField := target.id, value := expected }] :
        List DateRangeComputedInstance),
      ([] : List DateRangeComputedError)),
      (.presentValue expected, .presentValue unrelatedStored)) := by
  native_decide

/- Change classification is source-relative: an accepted value equal to the source target remains inert against a different destination. -/
example : (do
    let view ← resultView? "sku1" "sku2" (data false false)
      expected expectedRange
    let destination ← destination? true
    let applied ← view.applyToChecked destination |>.toOption
    pure (view.withoutErrors, view.withChanges, applied target.id)) =
    some (([{ targetField := target.id, value := expected }] :
        List DateRangeComputedInstance),
      ([] : List DateRangeComputedInstance),
      .presentValue priorStored) := by
  native_decide

/- Clean no-selection clears a source-filled target and materializes an absent destination target; reversed keyed endpoints retain their attempted range as a computed error. -/
example :
    (do
      let view ← resultView? "missing" "sku2" (data false false)
        priorStored priorRange
      let destination ← destination? false
      let applied ← view.applyToChecked destination |>.toOption
      pure (view.cleared, applied target.id, applied unrelatedTarget.id)) =
      some ([target.id], .presentEmpty, .presentValue unrelatedStored) ∧
    (do
      let view ← resultView? "sku2" "sku1" (data false false)
        priorStored priorRange
      let destination ← destination? true
      let applied ← view.applyToChecked destination |>.toOption
      pure (view.withErrors, view.noErrorOccurred, applied target.id)) =
      some ([{
        targetField := target.id
        attempted := invertedStored
        cause := .inverted
      }], false, .presentEmpty) := by
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
