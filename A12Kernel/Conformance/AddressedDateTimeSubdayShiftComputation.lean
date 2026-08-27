import A12Kernel.Elaboration.AddressedDateTimeSubdayShiftComputation

/-! # Exact-address repeatable DateTime sub-day shift locks -/

namespace A12Kernel.Conformance.AddressedDateTimeSubdayShiftComputation

open A12Kernel

private def numberField (id : FieldId) (name : String)
    (groupPath : GroupPath) (scope : List RepeatableLevel) : FlatFieldDecl := {
  id, name, groupPath, repeatableScope := scope
  policy := { kind := .number { scale := 0, signed := false } }
}

private def dateTimeField (id : FieldId) (name : String)
    (groupPath : GroupPath) (scope : List RepeatableLevel) : FlatFieldDecl := {
  id, name, groupPath, repeatableScope := scope
  policy := { kind := .temporal .dateTime TemporalComponents.now }
  temporalTargetPolicy := some { format := "yyyy-MM-dd'T'HH:mm:ss" }
}

private def rootAmount := numberField 1 "RootAmount" ["Order"] []
private def rowAmount :=
  numberField 2 "RowAmount" ["Order", "Projects", "Tasks"] [10, 20]
private def source :=
  dateTimeField 3 "ProjectStamp" ["Order", "Projects"] [10]
private def target :=
  dateTimeField 4 "CalculatedStamp" ["Order", "Projects", "Tasks"] [10, 20]
private def unrelated := dateTimeField 5 "Unrelated" ["Order"] []

private def model : FlatModel := {
  fields := [rootAmount, rowAmount, source, target, unrelated]
  repeatableGroups := [
    { level := 10, path := ["Order", "Projects"], repeatability := some 3 },
    { level := 20, path := ["Order", "Projects", "Tasks"], repeatability := some 3 }
  ]
  timeZoneId := "UTC"
}

private def absolute (groups : GroupPath) (field : String) : SurfaceFieldPath :=
  { base := .absolute, groups, field }

private def shiftAmount : AuthoredNumericExpr SurfaceNumericAtom :=
  .binary .add
    (.atom (.field (absolute ["Order", "Projects", "Tasks"] "RowAmount")))
    (.binary .add
      (.atom (.field (absolute ["Order"] "RootAmount")))
      (.atom (.field (absolute ["Order", "Projects", "Tasks"] "RowAmount"))))

private def operation? :=
  (checkAddressedDateTimeSubdayShiftComputation model
    ["Order", "Projects", "Tasks"] target.id
    (absolute ["Order", "Projects"] source.name) .hours shiftAmount).toOption

private def row (group : RepeatableLevel) (path : List Nat) : RowAddr :=
  { group, path }

private def address (field : FieldId) (path : List Nat) : CellAddr :=
  { field, path }

private def cell (field : FieldId) (path : List Nat)
    (stored : String) (raw : RawCell) : ClassifiedCellInput :=
  { address := { field, path }, stored, raw }

private def numberCell (field : FieldId) (path : List Nat) (value : Rat) :=
  cell field path (toString value) (.parsed (.num value))

private def clock (hour minute second : Nat)
    (valid : hour < 24 ∧ minute < 60 ∧ second < 60) : TimeOfDay :=
  ⟨hour, minute, second, valid⟩

private def dateTimeCell (field : FieldId) (path : List Nat)
    (text : String) (hour : Nat) (valid : hour < 24) :=
  cell field path text (.parsed (.temporal (.dateTime
    { epochMillis := hour * 3600000 }
    { year := 1970, month := 1, day := 1 }
    (clock hour 0 0 ⟨valid, by decide, by decide⟩) .storedGregorian)))

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
  numberCell rootAmount.id [] 1,
  numberCell rowAmount.id [1, 1] 1,
  numberCell rowAmount.id [1, 2] 2,
  numberCell rowAmount.id [2, 1] 3,
  dateTimeCell source.id [1] "1970-01-01T05:00:00" 5 (by decide),
  dateTimeCell source.id [2] "1970-01-01T10:00:00" 10 (by decide),
  dateTimeCell target.id [1, 1] "1970-01-01T08:00:00" 8 (by decide),
  dateTimeCell target.id [1, 2] "2000-01-01T06:00:00" 6 (by decide)]

private structure OutcomeSummary where
  source : CellAddr
  target : CellAddr
  value : Option String
  poison : Option FormalCause
  deriving Repr, DecidableEq

private def summarize (outcome : AddressedDateTimeSubdayShiftComputationOutcome) :
    OutcomeSummary := {
  source := outcome.sourceField
  target := outcome.targetField
  value := match outcome.outcome with
    | .accepted value => some value.text
    | .noValue | .poison _ => none
  poison := match outcome.outcome with
    | .poison cause => some cause
    | .accepted _ | .noValue => none
}

/- Each physical target row binds the enclosing source and its own amount, retaining exact source-first dependencies, references, addresses, and whole-DateTime results. -/
example :
    operation?.map (fun operation =>
      (operation.fieldDependencies,
        operation.referencesField source.id,
        operation.referencesField rowAmount.id,
        operation.referencesField rootAmount.id,
        operation.referencesField target.id)) =
      some ([source.id, rowAmount.id, rootAmount.id, rowAmount.id],
        true, true, true, false) ∧
    (do
      let operation ← operation?
      let input ← input?
      let outcomes ← operation.execute input |>.toOption
      pure (outcomes.map summarize)) = some [
        { source := address source.id [1], target := address target.id [1, 1],
          value := some "1970-01-01T08:00:00", poison := none },
        { source := address source.id [1], target := address target.id [1, 2],
          value := some "1970-01-01T10:00:00", poison := none },
        { source := address source.id [2], target := address target.id [2, 1],
          value := some "1970-01-01T17:00:00", poison := none }
      ] := by
  native_decide

/- A formal source hides its malformed row amount, while an empty source reaches that amount. -/
example :
    (do
      let operation ← operation?
      let input ← document? [
          row 10 [1], row 10 [2], row 20 [1, 1], row 20 [2, 1]] [
        numberCell rootAmount.id [] 1,
        cell rowAmount.id [1, 1] "bad" (.rejected .malformed),
        cell rowAmount.id [2, 1] "bad" (.rejected .malformed),
        cell source.id [1] "bad" (.rejected .dateFormat)]
      let outcomes ← operation.execute input |>.toOption
      pure (outcomes.map summarize)) = some [
        { source := address source.id [1], target := address target.id [1, 1],
          value := none, poison := some .dateFormat },
        { source := address source.id [2], target := address target.id [2, 1],
          value := none, poison := some .malformed }
      ] := by
  native_decide

/- No physical target row reaches the malformed amount. -/
example :
    (do
      let operation ← operation?
      let input ← document? [] [
        cell rootAmount.id [] "bad" (.rejected .malformed)]
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
    dateTimeCell target.id [1, 1] "2000-01-01T06:00:00" 6 (by decide),
    dateTimeCell unrelated.id [] "1970-01-01T03:00:00" 3 (by decide)]
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

/- Result classification remains source-relative, and separate-destination application consumes only retained exact-address actions. -/
example : resultApplicationSummary? = some {
    values := [
      (address target.id [1, 1], "1970-01-01T08:00:00"),
      (address target.id [1, 2], "1970-01-01T10:00:00"),
      (address target.id [2, 1], "1970-01-01T17:00:00")]
    changes := [
      (address target.id [1, 2], "1970-01-01T10:00:00"),
      (address target.id [2, 1], "1970-01-01T17:00:00")]
    cleared := []
    row11 := .presentValue (stored "2000-01-01T06:00:00")
    row12 := .presentValue (stored "1970-01-01T10:00:00")
    row21 := .presentValue (stored "1970-01-01T17:00:00")
    unrelatedState := .presentValue (stored "1970-01-01T03:00:00")
  } := by
  native_decide

/- A DateTime shift cannot read the repeatable DateTime target it computes. -/
example :
    (match checkAddressedDateTimeSubdayShiftComputation model
        ["Order", "Projects", "Tasks"] target.id
        (absolute ["Order", "Projects", "Tasks"] target.name)
        .hours shiftAmount with
      | .error (.targetSelfReference field) => field == target.id
      | _ => false) = true := by
  native_decide

/- A direct attempt to use the DateTime target as the numeric amount fails the amount-kind gate before target-reference exclusion. -/
example :
    (match checkAddressedDateTimeSubdayShiftComputation model
        ["Order", "Projects", "Tasks"] target.id
        (absolute ["Order", "Projects"] source.name)
        .hours (.atom (.field
          (absolute ["Order", "Projects", "Tasks"] target.name))) with
      | .error (.shift (.amount
          (.amountExpression (.fieldNotNumber path)))) =>
          path == target.path
      | _ => false) = true := by
  native_decide

end A12Kernel.Conformance.AddressedDateTimeSubdayShiftComputation
