import A12Kernel.Elaboration.AddressedTimeFromDateTime

/-! # Exact-address repeatable `TimeFromDateTime` result and application locks -/

namespace A12Kernel.Conformance.AddressedTimeFromDateTime

open A12Kernel

private def temporalField (id : FieldId) (name : String)
    (groupPath : GroupPath) (scope : List RepeatableLevel)
    (kind : TemporalKind) (components : TemporalComponents)
    (format : String) : FlatFieldDecl := {
  id, name, groupPath, repeatableScope := scope
  policy := { kind := .temporal kind components }
  temporalTargetPolicy := some { format, partialMode := .full }
}

private def source := temporalField 1 "SlotStamp"
  ["Schedule", "Slots"] [10]
  .dateTime TemporalComponents.now "yyyy-MM-dd'T'HH:mm:ss"

private def target := temporalField 2 "SlotTime"
  ["Schedule", "Slots"] [10]
  .time TemporalComponents.time "HH:mm:ss"

private def rootSource := temporalField 3 "ScheduleStamp" ["Schedule"] []
  .dateTime TemporalComponents.now "yyyy-MM-dd'T'HH:mm:ss"

private def rootTime := temporalField 4 "ScheduleTime" ["Schedule"] []
  .time TemporalComponents.time "HH:mm:ss"

private def model : FlatModel := {
  fields := [source, target, rootSource, rootTime]
  timeZoneId := "Europe/Berlin"
  repeatableGroups := [{
    level := 10, path := ["Schedule", "Slots"], repeatability := some 5
  }]
}

private def prepared :
    PreparedFlatStringContext model builtinStringPatternCompiler :=
  (prepareFlatStringContext { now := { epochMillis := 0 } }
    builtinStringPatternCompiler model).toOption.get (by native_decide)

private def bare (field : String) : SurfaceFieldPath :=
  { base := .relative 0, groups := [], field }

private def parent (field : String) : SurfaceFieldPath :=
  { base := .relative 1, groups := [], field }

private def operation? : Option (CheckedAddressedTimeFromDateTime model) :=
  (checkAddressedTimeFromDateTime model ["Schedule", "Slots"] target.id
    (bare source.name)).toOption

private def rootOperation? : Option (CheckedAddressedTimeFromDateTime model) :=
  (checkAddressedTimeFromDateTime model ["Schedule", "Slots"] target.id
    (parent rootSource.name)).toOption

/- Same-scope and enclosing root sources are both admitted by the target-bound scope rule. -/
example : operation?.isSome = true ∧ rootOperation?.isSome = true := by
  native_decide

private def incompleteSource := temporalField 5 "SlotClockOnly"
  ["Schedule", "Slots"] [10]
  .dateTime TemporalComponents.time "HH:mm:ss"

private def incompleteModel : FlatModel := {
  fields := [target, incompleteSource]
  timeZoneId := "Europe/Berlin"
  repeatableGroups := [{
    level := 10, path := ["Schedule", "Slots"], repeatability := some 5
  }]
}

private def deepSource := temporalField 6 "DetailStamp"
  ["Schedule", "Slots", "Details"] [10, 20]
  .dateTime TemporalComponents.now "yyyy-MM-dd'T'HH:mm:ss"

private def deepSourceModel : FlatModel := {
  fields := [target, deepSource]
  timeZoneId := "Europe/Berlin"
  repeatableGroups := [
    { level := 10, path := ["Schedule", "Slots"], repeatability := some 5 },
    { level := 20, path := ["Schedule", "Slots", "Details"],
      repeatability := some 5 }
  ]
}

private def child (group field : String) : SurfaceFieldPath :=
  { base := .relative 0, groups := [group], field }

private def elabError? (checked :
    Except AddressedTimeFromDateTimeElabError
      (CheckedAddressedTimeFromDateTime checkedModel)) :
    Option AddressedTimeFromDateTimeElabError :=
  match checked with
  | .error cause => some cause
  | .ok _ => none

/- Target ownership, target repetition, complete-DateTime admission, and source-scope binding are four distinct
addressed gates. The first row is this family's own narrower boundary, not a Kernel refusal: this family still
carries an equality placement gate rather than the shared repeatable-target certificate's containment, so it
refuses the ancestor `["Schedule"]` that the Kernel admits. The
[declaring-group gate checkpoint](../../docs/SOURCES.md#src-computation-declaring-group-gate) owns the
measurement and [SG4](../../docs/SEMANTICS-GAPS.md#sg4--computation-scheduling-and-state-transition) tracks the
remaining families. -/
example :
    elabError? (checkAddressedTimeFromDateTime model ["Schedule"]
      target.id (parent rootSource.name)) =
        some (.targetOutsideDeclaringGroup target.path ["Schedule"]) ∧
    elabError? (checkAddressedTimeFromDateTime model ["Schedule"]
      rootTime.id (bare rootSource.name)) =
        some (.targetNotRepeatable rootTime.path) ∧
    elabError? (checkAddressedTimeFromDateTime incompleteModel
      ["Schedule", "Slots"] target.id (bare incompleteSource.name)) =
        some (.source (.sourceComponents incompleteSource.id
          TemporalComponents.time)) ∧
    elabError? (checkAddressedTimeFromDateTime deepSourceModel
      ["Schedule", "Slots"] target.id
      (child "Details" deepSource.name)) =
        some (.source (.scopeMismatch target.path deepSource.path)) := by
  native_decide

private def momentAt (day hour minute : Nat) : Option TemporalValue := do
  let wall ← LocalDateTime.ofYmdHms? 2024 6 day hour minute 0
  let instant ← ModelZone.ConcreteProfile.europeBerlin.resolveLocal? wall
  pure (.dateTime instant wall.date.civil.parts wall.time .storedGregorian)

private def sourceCell (field : FieldId) (path : List Nat)
    (stored : String) (raw : RawCell) : ClassifiedCellInput := {
  address := { field, path }
  stored
  raw
}

private def timeCell (field : FieldId) (path : List Nat)
    (stored : String) (time : TimeOfDay) : ClassifiedCellInput := {
  address := { field, path }
  stored
  raw := .parsed (.temporal (.time { epochMillis := 0 } time))
}

private def inputForRows? (rows : List Nat)
    (cells : List ClassifiedCellInput) :
    Option (CheckedDocument model) :=
  (checkDocument prepared "en_US" {
    instantiatedRows := rows.map fun index =>
      { group := 10, path := [index] }
    cells
  }).toOption

private def input? (rowCount : Nat) (cells : List ClassifiedCellInput) :
    Option (CheckedDocument model) :=
  inputForRows? ((List.range rowCount).map fun index => index + 1) cells

private def outcomeTriples?
    (operation : CheckedAddressedTimeFromDateTime model)
    (rowCount : Nat) (cells : List ClassifiedCellInput) :
    Option (List (CellAddr × CellAddr × TimeTargetOutcome)) := do
  let input ← input? rowCount cells
  let outcomes ← operation.execute input |>.toOption
  pure (outcomes.map fun entry =>
    (entry.sourceField, entry.targetField, entry.outcome))

private def address (field : FieldId) (path : List Nat) : CellAddr :=
  { field, path }

private def storedTime (text : String) (nonempty : text ≠ "" := by decide) :
    StoredTime := ⟨text, nonempty⟩

/- Same-scope rows retain exact addresses and the source wall clock, while clean absence and formal poison stay row-local. -/
example : (do
    let operation ← operation?
    outcomeTriples? operation 3 [
      sourceCell source.id [1] "2024-06-15T00:30:00"
        (.parsed (.temporal (momentAt 15 0 30 |>.get (by native_decide)))),
      sourceCell source.id [3] "bad" (.rejected .dateFormat)]) = some [
      (address source.id [1], address target.id [1],
        .accepted (storedTime "00:30:00")),
      (address source.id [2], address target.id [2], .noValue),
      (address source.id [3], address target.id [3], .poison .dateFormat)
    ] := by
  native_decide

private def transientOutcomeTriples? :
    Option (List (CellAddr × CellAddr × TimeTargetOutcome)) := do
  let operation ← operation?
  let input ← input? 2 [
    sourceCell source.id [1] "2024-06-15T00:30:00"
      (.parsed (.temporal (momentAt 15 0 30 |>.get (by native_decide)))),
    sourceCell source.id [2] "2024-06-16T13:45:00"
      (.parsed (.temporal (momentAt 16 13 45 |>.get (by native_decide))))]
  let transient ← input? 2 [
    sourceCell source.id [1] "2024-06-16T23:45:00"
      (.parsed (.temporal (momentAt 16 23 45 |>.get (by native_decide)))),
    sourceCell source.id [2] "bad" (.rejected .dateFormat)]
  let outcomes ← operation.executeWithRead input transient.read |>.toOption
  pure (outcomes.map fun entry =>
    (entry.sourceField, entry.targetField, entry.outcome))

/- Caller-supplied source state controls reached extraction while immutable target-row topology and exact addresses remain unchanged. -/
example : transientOutcomeTriples? = some [
    (address source.id [1], address target.id [1],
      .accepted (storedTime "23:45:00")),
    (address source.id [2], address target.id [2],
      .poison .dateFormat)
  ] := by
  native_decide

/- Physical target-row encounter order is observable and must not be replaced by coordinate sorting. -/
example : (do
    let operation ← operation?
    let input ← inputForRows? [3, 1, 2] []
    let outcomes ← operation.execute input |>.toOption
    pure (outcomes.map (fun entry => entry.targetField))) = some [
      address target.id [3], address target.id [1], address target.id [2]
    ] := by
  native_decide

/- One root source fans out from its own address to every physical target row; no physical rows produce no outcomes. -/
example : (do
    let operation ← rootOperation?
    let rows ← outcomeTriples? operation 2 [
      sourceCell rootSource.id [] "2024-06-16T13:45:00"
        (.parsed (.temporal (momentAt 16 13 45 |>.get (by native_decide))))]
    let none ← outcomeTriples? operation 0 []
    pure (rows, none)) = some ([
      (address rootSource.id [], address target.id [1],
        .accepted (storedTime "13:45:00")),
      (address rootSource.id [], address target.id [2],
        .accepted (storedTime "13:45:00"))], []) := by
  native_decide

private def nestedSource := temporalField 11 "MilestoneStamp"
  ["Project", "Milestones"] [10]
  .dateTime TemporalComponents.now "yyyy-MM-dd'T'HH:mm:ss"

private def nestedTarget := temporalField 12 "TaskTime"
  ["Project", "Milestones", "Tasks"] [10, 20]
  .time TemporalComponents.time "HH:mm:ss"

private def nestedModel : FlatModel := {
  fields := [nestedSource, nestedTarget]
  timeZoneId := "Europe/Berlin"
  repeatableGroups := [
    { level := 10, path := ["Project", "Milestones"], repeatability := some 5 },
    { level := 20, path := ["Project", "Milestones", "Tasks"],
      repeatability := some 5 }
  ]
}

private def nestedPrepared :
    PreparedFlatStringContext nestedModel builtinStringPatternCompiler :=
  (prepareFlatStringContext { now := { epochMillis := 0 } }
    builtinStringPatternCompiler nestedModel).toOption.get (by native_decide)

private def nestedOperation? :
    Option (CheckedAddressedTimeFromDateTime nestedModel) :=
  (checkAddressedTimeFromDateTime nestedModel
    ["Project", "Milestones", "Tasks"] nestedTarget.id
    (parent nestedSource.name)).toOption

private def nestedRows : List RowAddr :=
  [{ group := 10, path := [1] }, { group := 10, path := [2] },
    { group := 20, path := [1, 1] }, { group := 20, path := [1, 2] },
    { group := 20, path := [2, 1] }, { group := 20, path := [2, 2] }]

private def nestedInput? (cells : List ClassifiedCellInput) :
    Option (CheckedDocument nestedModel) :=
  (checkDocument nestedPrepared "en_US" {
    instantiatedRows := nestedRows
    cells
  }).toOption

private def nestedTriples? (cells : List ClassifiedCellInput) :
    Option (List (CellAddr × CellAddr × TimeTargetOutcome)) := do
  let operation ← nestedOperation?
  let input ← nestedInput? cells
  let outcomes ← operation.execute input |>.toOption
  pure (outcomes.map fun entry =>
    (entry.sourceField, entry.targetField, entry.outcome))

/- Enclosing sources correlate only to their own leaves; borrowing the full target path or reading one global source cannot satisfy this matrix. -/
example : nestedTriples? [
    sourceCell nestedSource.id [1] "bad" (.rejected .dateFormat),
    sourceCell nestedSource.id [2] "2024-06-16T23:45:00"
      (.parsed (.temporal (momentAt 16 23 45 |>.get (by native_decide))))] = some [
      (address nestedSource.id [1], address nestedTarget.id [1, 1],
        .poison .dateFormat),
      (address nestedSource.id [1], address nestedTarget.id [1, 2],
        .poison .dateFormat),
      (address nestedSource.id [2], address nestedTarget.id [2, 1],
        .accepted (storedTime "23:45:00")),
      (address nestedSource.id [2], address nestedTarget.id [2, 2],
        .accepted (storedTime "23:45:00"))
    ] := by
  native_decide

private structure ResultApplicationSummary where
  values : List (CellAddr × String)
  changes : List (CellAddr × String)
  cleared : List CellAddr
  row1 : TimeTargetState
  row2 : TimeTargetState
  unrelatedState : TimeTargetState
  deriving Repr, DecidableEq

private def resultApplicationSummary? : Option ResultApplicationSummary := do
  let operation ← operation?
  let input ← input? 2 [
    sourceCell source.id [1] "2024-06-15T00:30:00"
      (.parsed (.temporal (momentAt 15 0 30 |>.get (by native_decide)))),
    sourceCell source.id [2] "2024-06-16T13:45:00"
      (.parsed (.temporal (momentAt 16 13 45 |>.get (by native_decide)))),
    timeCell target.id [1] "00:30:00" ⟨0, 30, 0, by decide⟩,
    timeCell target.id [2] "07:15:00" ⟨7, 15, 0, by decide⟩]
  let destination ← input? 2 [
    timeCell target.id [1] "06:00:00" ⟨6, 0, 0, by decide⟩,
    timeCell rootTime.id [] "08:45:00" ⟨8, 45, 0, by decide⟩]
  let result ← operation.executeResult input ([] : List FormalCause) |>.toOption
  let applied ← result.applyToChecked destination |>.toOption
  pure {
    values := result.time.withoutErrors.map fun item =>
      (item.targetField, item.value.text)
    changes := result.time.withChanges.map fun item =>
      (item.targetField, item.value.text)
    cleared := result.time.cleared
    row1 := applied (address target.id [1])
    row2 := applied (address target.id [2])
    unrelatedState := applied (address rootTime.id [])
  }

/- Exact keys omit the source-identical action, materialize a changed absent destination cell, and preserve unrelated state. -/
example : resultApplicationSummary? = some {
    values := [
      (address target.id [1], "00:30:00"),
      (address target.id [2], "13:45:00")]
    changes := [
      (address target.id [2], "13:45:00")]
    cleared := []
    row1 := .presentValue (storedTime "06:00:00")
    row2 := .presentValue (storedTime "13:45:00")
    unrelatedState := .presentValue (storedTime "08:45:00")
  } := by
  native_decide

private def clearedApplicationSummary? :
    Option (List CellAddr × List FormalCause × Bool ×
      TimeTargetState × TimeTargetState) := do
  let operation ← operation?
  let input ← input? 2 [
    timeCell target.id [1] "06:00:00" ⟨6, 0, 0, by decide⟩,
    sourceCell source.id [2] "bad" (.rejected .dateFormat),
    timeCell target.id [2] "07:15:00" ⟨7, 15, 0, by decide⟩]
  let destination ← input? 2 []
  let result ← operation.executeResult input [.dateFormat] |>.toOption
  let applied ← result.applyToChecked destination |>.toOption
  pure (result.time.cleared, result.time.formalErrorsInOperands,
    result.time.noErrorOccurred,
    applied (address target.id [1]), applied (address target.id [2]))

/- Exact target-state lookup classifies absent-source and poisoned rows as retained clears at their own filled addresses, then applies both to an empty destination. -/
example : clearedApplicationSummary? = some (
    [address target.id [1], address target.id [2]],
    [.dateFormat], false, .presentEmpty, .presentEmpty) := by
  native_decide

end A12Kernel.Conformance.AddressedTimeFromDateTime
