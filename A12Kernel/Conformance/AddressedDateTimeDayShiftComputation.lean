import A12Kernel.Elaboration.AddressedDateTimeDayShiftComputation

/-! # Exact-address repeatable DateTime calendar-day shift locks -/

namespace A12Kernel.Conformance.AddressedDateTimeDayShiftComputation

open A12Kernel

private def numberField (id : FieldId) (name : String)
    (groupPath : GroupPath) (scope : List RepeatableLevel) : FlatFieldDecl := {
  id, name, groupPath, repeatableScope := scope
  policy := { kind := .number { scale := 0, signed := true } }
}

private def dateTimeField (id : FieldId) (name : String)
    (groupPath : GroupPath) (scope : List RepeatableLevel) : FlatFieldDecl := {
  id, name, groupPath, repeatableScope := scope
  policy := { kind := .temporal .dateTime TemporalComponents.now }
  temporalTargetPolicy := some { format := "yyyy-MM-dd'T'HH:mm:ss" }
}

private def amount :=
  numberField 1 "Days" ["Order", "Projects", "Tasks"] [10, 20]
private def source :=
  dateTimeField 2 "ProjectStamp" ["Order", "Projects"] [10]
private def target :=
  dateTimeField 3 "CalculatedStamp" ["Order", "Projects", "Tasks"] [10, 20]
private def unrelated := dateTimeField 4 "Unrelated" ["Order"] []

private def model : FlatModel := {
  fields := [amount, source, target, unrelated]
  repeatableGroups := [
    { level := 10, path := ["Order", "Projects"], repeatability := some 3 },
    { level := 20, path := ["Order", "Projects", "Tasks"], repeatability := some 3 }
  ]
  timeZoneId := "Europe/Berlin"
}

private def absolute (groups : GroupPath) (field : String) : SurfaceFieldPath :=
  { base := .absolute, groups, field }

private def operation? :=
  (checkAddressedDateTimeDayShiftComputation model
    ["Order", "Projects", "Tasks"] target.id
    (absolute ["Order", "Projects"] source.name)
    (absolute ["Order", "Projects", "Tasks"] amount.name)).toOption

private def row (group : RepeatableLevel) (path : List Nat) : RowAddr :=
  { group, path }

private def address (field : FieldId) (path : List Nat) : CellAddr :=
  { field, path }

private def cell (field : FieldId) (path : List Nat)
    (stored : String) (raw : RawCell) : ClassifiedCellInput :=
  { address := { field, path }, stored, raw }

private def numberCell (path : List Nat) (value : Rat) :=
  cell amount.id path (toString value) (.parsed (.num value))

private def temporalRawOf (declaration : FlatFieldDecl) (text : String) : RawCell :=
  match (certifyDateTimeInputField declaration).toOption with
  | none => .rejected .dateFormat
  | some checked =>
      match checked.classifyStoredForModel model.timeZoneId text with
      | .ok raw => raw
      | .error _ => .rejected .dateFormat

private def dateTimeCell (declaration : FlatFieldDecl) (path : List Nat)
    (text : String) : ClassifiedCellInput :=
  cell declaration.id path text (temporalRawOf declaration text)

private def prepared : PreparedFlatStringContext model
    builtinStringPatternCompiler :=
  (prepareFlatStringContext { now := { epochMillis := 0 } }
    builtinStringPatternCompiler model).toOption.get (by native_decide)

private def rows := [
  row 10 [1], row 10 [2],
  row 20 [1, 1], row 20 [1, 2], row 20 [2, 1]]

private def document? (actualRows : List RowAddr)
    (cells : List ClassifiedCellInput) : Option (CheckedDocument model) :=
  (checkDocument prepared "en_US" {
    instantiatedRows := actualRows, cells }).toOption

private def input? := document? rows [
  numberCell [1, 1] 1,
  numberCell [1, 2] 0,
  numberCell [2, 1] (-1),
  dateTimeCell source [1] "2024-03-30T02:30:00",
  dateTimeCell source [2] "1916-05-01T23:30:00",
  dateTimeCell target [1, 1] "2024-03-31T01:30:00",
  dateTimeCell target [1, 2] "2024-03-29T02:30:00"]

private structure OutcomeSummary where
  source : CellAddr
  target : CellAddr
  value : Option String
  poison : Option FormalCause
  deriving Repr, DecidableEq

private def summarize (entry : AddressedDateTimeDayShiftComputationOutcome) :
    OutcomeSummary := {
  source := entry.sourceField
  target := entry.targetField
  value := match entry.outcome with
    | .accepted value => some value.text
    | .noValue | .poison _ => none
  poison := match entry.outcome with
    | .poison cause => some cause
    | .accepted _ | .noValue => none
}

/- Outer DateTime correlation and target-row Number reads retain exact coordinates. The values separate a Berlin spring gap, exact zero preservation, and the historical source-offset fallback from elapsed shifting. -/
example :
    operation?.map (fun operation =>
      (operation.fieldDependencies,
        operation.referencesField source.id,
        operation.referencesField amount.id,
        operation.referencesField target.id)) =
      some ([source.id, amount.id], true, true, false) ∧
    (do
      let operation ← operation?
      let input ← input?
      let outcomes ← operation.execute input |>.toOption
      pure (outcomes.map summarize)) = some [
        { source := address source.id [1], target := address target.id [1, 1],
          value := some "2024-03-31T01:30:00", poison := none },
        { source := address source.id [1], target := address target.id [1, 2],
          value := some "2024-03-30T02:30:00", poison := none },
        { source := address source.id [2], target := address target.id [2, 1],
          value := some "1916-04-30T22:30:00", poison := none }
      ] := by
  native_decide

/- A formal source hides its malformed amount. An absent source reaches its amount, preserving either reached poison or cause-free no-value. -/
example :
    (do
      let operation ← operation?
      let input ← document? [
          row 10 [1], row 10 [2], row 10 [3],
          row 20 [1, 1], row 20 [2, 1], row 20 [3, 1]] [
        cell amount.id [1, 1] "bad" (.rejected .malformed),
        cell amount.id [2, 1] "bad" (.rejected .malformed),
        numberCell [3, 1] 1,
        cell source.id [1] "bad" (.rejected .dateFormat)]
      let outcomes ← operation.execute input |>.toOption
      pure (outcomes.map summarize)) = some [
        { source := address source.id [1], target := address target.id [1, 1],
          value := none, poison := some .dateFormat },
        { source := address source.id [2], target := address target.id [2, 1],
          value := none, poison := some .malformed },
        { source := address source.id [3], target := address target.id [3, 1],
          value := none, poison := none }
      ] := by
  native_decide

/- The checked-plan inventory is eager rather than a runtime trace: it retains the hidden malformed amount and source, while the computed target and unrelated field remain outside the operand set. -/
example :
    (do
      let operation ← operation?
      let input ← document? [row 10 [1], row 20 [1, 1]] [
        cell target.id [1, 1] "bad" (.rejected .dateFormat),
        cell unrelated.id [] "bad" (.rejected .dateFormat),
        cell amount.id [1, 1] "bad" (.rejected .malformed),
        cell source.id [1] "bad" (.rejected .dateFormat)]
      let result ← operation.executeResultWithFormalInputs input |>.toOption
      let findings := result.dateTime.formalErrorsInOperands
      pure (
        findings.length,
        findings.contains {
          address := address amount.id [1, 1], cause := .malformed },
        findings.contains {
          address := address source.id [1], cause := .dateFormat },
        findings.any fun finding => finding.address.field == target.id,
        findings.any fun finding => finding.address.field == unrelated.id)) =
      some (2, true, true, false, false) := by
  native_decide

private def indexedModel : FlatModel := {
  model with
  repeatableGroups := [
    { level := 10, path := ["Order", "Projects"], repeatability := some 3 },
    { level := 20, path := ["Order", "Projects", "Tasks"],
      repeatability := some 3, indexField := some amount.id }
  ]
}

private def indexedPrepared : PreparedFlatStringContext indexedModel
    builtinStringPatternCompiler :=
  (prepareFlatStringContext { now := { epochMillis := 0 } }
    builtinStringPatternCompiler indexedModel).toOption.get (by native_decide)

private def indexedOperation? :
    Option (CheckedAddressedDateTimeDayShiftComputation indexedModel) :=
  (checkAddressedDateTimeDayShiftComputation indexedModel
    ["Order", "Projects", "Tasks"] target.id
    (absolute ["Order", "Projects"] source.name)
    (absolute ["Order", "Projects", "Tasks"] amount.name)).toOption

private def indexedInput? (sourceCell : ClassifiedCellInput) :
    Option (CheckedDocument indexedModel) :=
  (checkDocument indexedPrepared "en_US" {
    instantiatedRows := [
      row 10 [1], row 20 [1, 1], row 20 [1, 2]
    ]
    cells := [
      sourceCell,
      numberCell [1, 1] 1,
      numberCell [1, 2] 1,
      dateTimeCell target [1, 1] "2024-03-31T01:30:00",
      dateTimeCell target [1, 2] "2024-03-31T01:30:00"
    ]
  }).toOption

private def indexedFinding (field : FieldId) (path : List Nat)
    (cause : FormalCause) : ComputationFormalInputFinding := {
  address := address field path
  cause
}

private def indexedResultSummary?
    (sourceCell : ClassifiedCellInput) : Option
      (List ComputationFormalInputFinding ×
        List (CellAddr × String) × List CellAddr) := do
  let operation ← indexedOperation?
  let input ← indexedInput? sourceCell
  let result ← operation.executeResultWithFormalInputs input |>.toOption
  pure (
    result.dateTime.formalErrorsInOperands,
    result.dateTime.withoutErrors.map fun item =>
      (item.targetField, item.value.text),
    result.dateTime.cleared)

private def indexedPreparedOutcomeSummary?
    (sourceCell : ClassifiedCellInput) : Option (List OutcomeSummary) := do
  let operation ← indexedOperation?
  let input ← indexedInput? sourceCell
  let plan ← operation.formalInputPlan |>.toOption
  let prepared ← plan.prepare input |>.toOption
  let outcomes ← (operation.executeWithAmountRead input
    fun environment field =>
      (input.checkedCellWithRead prepared.preliminary.readComputation
        environment field).map some).toOption
  pure (outcomes.map summarize)

/- Reached duplicate-index day amounts remain eager findings, poison both calendar landings, and clear both source-filled targets. -/
example : indexedResultSummary?
    (dateTimeCell source [1] "2024-03-30T02:30:00") = some ([
      indexedFinding amount.id [1, 1] .duplicateIndex,
      indexedFinding amount.id [1, 2] .duplicateIndex
    ], [], [
      address target.id [1, 1],
      address target.id [1, 2]
    ]) := by
  native_decide

/- Prepared execution attaches the duplicate cause at the reached amount boundary. -/
example : indexedPreparedOutcomeSummary?
    (dateTimeCell source [1] "2024-03-30T02:30:00") = some [
      { source := address source.id [1],
        target := address target.id [1, 1],
        value := none, poison := some .duplicateIndex },
      { source := address source.id [1],
        target := address target.id [1, 2],
        value := none, poison := some .duplicateIndex }
    ] := by
  native_decide

/- An earlier formal DateTime source does not remove the generated amount findings from the whole-call inventory. -/
example : indexedResultSummary?
    (cell source.id [1] "bad" (.rejected .dateFormat)) = some ([
      indexedFinding source.id [1] .dateFormat,
      indexedFinding amount.id [1, 1] .duplicateIndex,
      indexedFinding amount.id [1, 2] .duplicateIndex
    ], [], [
      address target.id [1, 1],
      address target.id [1, 2]
    ]) := by
  native_decide

/- The immutable DateTime source remains first, so its formal cause hides the prepared amount poison at runtime. -/
example : indexedPreparedOutcomeSummary?
    (cell source.id [1] "bad" (.rejected .dateFormat)) = some [
      { source := address source.id [1],
        target := address target.id [1, 1],
        value := none, poison := some .dateFormat },
      { source := address source.id [1],
        target := address target.id [1, 2],
        value := none, poison := some .dateFormat }
    ] := by
  native_decide

example : (do
    let operation ← operation?
    let input ← document? [] []
    operation.execute input |>.toOption) = some [] := by
  native_decide

private def stored (text : String) (nonempty : text ≠ "" := by decide) :
    StoredDateTime := { text, nonempty }

private structure ResultApplicationSummary where
  values : List (CellAddr × String)
  changes : List (CellAddr × String)
  cleared : List CellAddr
  row11 : DateTimeTargetState
  row12 : DateTimeTargetState
  row21 : DateTimeTargetState
  unrelatedState : DateTimeTargetState
  deriving Repr, DecidableEq

private def resultApplicationSummary? : Option ResultApplicationSummary := do
  let operation ← operation?
  let input ← input?
  let destination ← document? rows [
    dateTimeCell target [1, 1] "2000-01-01T06:00:00",
    dateTimeCell target [2, 1] "2000-01-01T07:00:00",
    dateTimeCell unrelated [] "1970-01-01T03:00:00"]
  let result ← operation.executeResult input ([] : List FormalCause) |>.toOption
  let applied ← result.applyToChecked destination |>.toOption
  pure {
    values := result.dateTime.withoutErrors.map fun item =>
      (item.targetField, item.value.text)
    changes := result.dateTime.withChanges.map fun item =>
      (item.targetField, item.value.text)
    cleared := result.dateTime.cleared
    row11 := applied (address target.id [1, 1])
    row12 := applied (address target.id [1, 2])
    row21 := applied (address target.id [2, 1])
    unrelatedState := applied (address unrelated.id [])
  }

/- Result classification stays relative to immutable source target cells. Separate-destination application consumes only retained exact-address actions. -/
example : resultApplicationSummary? = some {
    values := [
      (address target.id [1, 1], "2024-03-31T01:30:00"),
      (address target.id [1, 2], "2024-03-30T02:30:00"),
      (address target.id [2, 1], "1916-04-30T22:30:00")]
    changes := [
      (address target.id [1, 2], "2024-03-30T02:30:00"),
      (address target.id [2, 1], "1916-04-30T22:30:00")]
    cleared := []
    row11 := .presentValue (stored "2000-01-01T06:00:00")
    row12 := .presentValue (stored "2024-03-30T02:30:00")
    row21 := .presentValue (stored "1916-04-30T22:30:00")
    unrelatedState := .presentValue (stored "1970-01-01T03:00:00")
  } := by
  native_decide

/- The target is excluded whether reached as the DateTime source or rejected first by the Number-amount gate. -/
example :
    (match checkAddressedDateTimeDayShiftComputation model
        ["Order", "Projects", "Tasks"] target.id
        (absolute ["Order", "Projects", "Tasks"] target.name)
        (absolute ["Order", "Projects", "Tasks"] amount.name) with
      | .error (.targetSelfReference field) => field == target.id
      | _ => false) = true ∧
    (match checkAddressedDateTimeDayShiftComputation model
        ["Order", "Projects", "Tasks"] target.id
        (absolute ["Order", "Projects"] source.name)
        (absolute ["Order", "Projects", "Tasks"] target.name) with
      | .error (.amount (.amountExpression (.fieldNotNumber path))) =>
          path == target.path
      | _ => false) = true := by
  native_decide

end A12Kernel.Conformance.AddressedDateTimeDayShiftComputation
