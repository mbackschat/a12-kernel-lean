import A12Kernel.Elaboration.AddressedDateFromDateTime
import A12Kernel.Elaboration.FullDateComputationApplication

/-! # Repeatable `DateFromDateTime` locks

A DateTime source at the target scope or an enclosing scope computes one full-Date target per physically instantiated row. The cases retain both exact addresses, separate clean absence from row-local formal poison, and pin two-level enclosing-row correlation. -/

namespace A12Kernel.Conformance.AddressedDateFromDateTime

open A12Kernel

private def temporalField (id : FieldId) (name : String) (kind : TemporalKind)
    (components : TemporalComponents) (format : String) : FlatFieldDecl := {
  id, name, groupPath := ["Schedule", "Slots"], repeatableScope := [10]
  policy := { kind := .temporal kind components }
  temporalTargetPolicy := some { format, partialMode := .full }
}

private def source := temporalField 1 "SlotStamp" .dateTime TemporalComponents.now "yyyy-MM-dd'T'HH:mm:ss"
private def target := temporalField 2 "SlotDate" .date TemporalComponents.fullDate "yyyy-MM-dd"
private def rootTarget : FlatFieldDecl := {
  target with id := 3, name := "PlannedDate", groupPath := ["Schedule"], repeatableScope := [] }
private def outerSource : FlatFieldDecl := {
  source with id := 4, name := "ScheduleStamp", groupPath := ["Schedule"], repeatableScope := [] }

private def model : FlatModel := {
  fields := [source, target, rootTarget, outerSource]
  timeZoneId := "Europe/Berlin"
  repeatableGroups := [{
    level := 10, path := ["Schedule", "Slots"], repeatability := some 5
  }]
}

private def prepared : PreparedFlatStringContext model builtinStringPatternCompiler :=
  (prepareFlatStringContext { now := { epochMillis := 0 } }
    builtinStringPatternCompiler model).toOption.get (by native_decide)

private def bare (field : String) : SurfaceFieldPath :=
  { base := .relative 0, groups := [], field }

private def parent (field : String) : SurfaceFieldPath :=
  { base := .relative 1, groups := [], field }

private def operation? : Option (CheckedAddressedDateFromDateTime model) :=
  (checkAddressedDateFromDateTime model ["Schedule", "Slots"] target.id
    (bare "SlotStamp")).toOption

private def outerOperation? : Option (CheckedAddressedDateFromDateTime model) :=
  (checkAddressedDateFromDateTime model ["Schedule", "Slots"] target.id
    (parent "ScheduleStamp")).toOption

private def momentAt (day hour minute : Nat) : Option TemporalValue := do
  let wall ← LocalDateTime.ofYmdHms? 2024 6 day hour minute 0
  let instant ← ModelZone.ConcreteProfile.europeBerlin.resolveLocal? wall
  pure (.dateTime instant wall.date.civil.parts wall.time .storedGregorian)

private def sourceCell (row : Nat) (stored : String) (raw : RawCell) : ClassifiedCellInput :=
  { address := { field := source.id, path := [row] }, stored, raw }

private def outerCell (stored : String) (raw : RawCell) : ClassifiedCellInput :=
  { address := { field := outerSource.id, path := [] }, stored, raw }

private def input? (rowCount : Nat) (cells : List ClassifiedCellInput) :
    Option (CheckedDocument model) :=
  (checkDocument prepared "en_US" {
    instantiatedRows := (List.range rowCount).map fun i => { group := 10, path := [i + 1] }
    cells
  }).toOption

private def outcomes? (rowCount : Nat) (cells : List ClassifiedCellInput) :
    Option (List (CellAddr × CellAddr × FullDateTargetOutcome)) := do
  let operation ← operation?
  let input ← input? rowCount cells
  let outcomes ← (operation.execute input).toOption
  pure (outcomes.map fun entry => (entry.sourceField, entry.targetField, entry.outcome))

private def outerOutcomes? (rowCount : Nat) (cells : List ClassifiedCellInput) :
    Option (List (CellAddr × CellAddr × FullDateTargetOutcome)) := do
  let operation ← outerOperation?
  let input ← input? rowCount cells
  let outcomes ← (operation.execute input).toOption
  pure (outcomes.map fun entry => (entry.sourceField, entry.targetField, entry.outcome))

private def address (field : FieldId) (row : Nat) : CellAddr := { field, path := [row] }

private def accepted (text : String) (nonempty : text ≠ "" := by decide) : FullDateTargetOutcome := .accepted { text, nonempty }

private def dateAt (day : Nat) : Value :=
  match momentAt day 0 0 with
  | some (.dateTime instant parts _ basis) =>
      .temporal (.date { instant, parts, basis })
  | _ => .temporal (.date {
      instant := { epochMillis := 0 }
      parts := { year := 2024, month := 6, day }
      basis := .storedGregorian
    })

private def targetCell (row : Nat) (stored : String) (day : Nat) :
    ClassifiedCellInput := {
  address := address target.id row
  stored
  raw := .parsed (dateAt day)
}

private def rootTargetCell (stored : String) (day : Nat) :
    ClassifiedCellInput := {
  address := { field := rootTarget.id, path := [] }
  stored
  raw := .parsed (dateAt day)
}

private structure ResultApplicationSummary where
  values : List (CellAddr × String)
  changes : List (CellAddr × String)
  errors : List CellAddr
  cleared : List CellAddr
  residual : List FormalCause
  row1 : FullDateTargetState
  row2 : FullDateTargetState
  unrelated : FullDateTargetState
  deriving Repr, DecidableEq

private def resultApplicationSummary? (input destination : CheckedDocument model)
    (residualMessages : List FormalCause := []) :
    Option ResultApplicationSummary := do
  let operation ← operation?
  let result ← operation.executeResult input residualMessages |>.toOption
  let applied ← result.applyToChecked destination |>.toOption
  pure {
    values := result.fullDate.withoutErrors.map fun item =>
      (item.targetField, item.value.text)
    changes := result.fullDate.withChanges.map fun item =>
      (item.targetField, item.value.text)
    errors := result.fullDate.withErrors.map (·.targetField)
    cleared := result.fullDate.cleared
    residual := result.fullDate.formalErrorsInOperands
    row1 := applied (address target.id 1)
    row2 := applied (address target.id 2)
    unrelated := applied { field := rootTarget.id, path := [] }
  }

/- The same-scope operation is admitted. The scalar carrier is the measured missing-wildcard control. -/
example : operation?.isSome = true ∧
    (match elaborateDateFromDateTimeComputation model source.id rootTarget.id with
      | .error (.source (.source (.repeatableReference path))) => path == source.path
      | _ => false) = true := by
  native_decide

/- Two rows retain their own source and target keys and extract their own wall-label dates. -/
example :
    outcomes? 2 [
      sourceCell 1 "2024-06-15T00:30:00"
        (.parsed (.temporal (momentAt 15 0 30 |>.get (by native_decide)))),
      sourceCell 2 "2024-06-16T13:45:00"
        (.parsed (.temporal (momentAt 16 13 45 |>.get (by native_decide))))
    ] = some [
      (address source.id 1, address target.id 1, accepted "2024-06-15"),
      (address source.id 2, address target.id 2, accepted "2024-06-16")
    ] := by
  native_decide

/- Clean absence and formal invalidity remain distinct row-local outcomes with exact source pointers. -/
example :
    outcomes? 3 [
      sourceCell 1 "2024-06-15T00:30:00"
        (.parsed (.temporal (momentAt 15 0 30 |>.get (by native_decide)))),
      sourceCell 3 "bad" (.rejected .dateFormat)
    ] = some [
      (address source.id 1, address target.id 1, accepted "2024-06-15"),
      (address source.id 2, address target.id 2, .noValue),
      (address source.id 3, address target.id 3, .poison .dateFormat)
    ] := by
  native_decide

example : outcomes? 0 [] = some [] := by
  native_decide

/- Exact row keys keep source-relative unchanged and changed actions distinct even when both rows share one target field ID. -/
example : (do
    let input ← input? 2 [
      sourceCell 1 "2024-06-15T00:30:00"
        (.parsed (.temporal (momentAt 15 0 30 |>.get (by native_decide)))),
      sourceCell 2 "2024-06-16T13:45:00"
        (.parsed (.temporal (momentAt 16 13 45 |>.get (by native_decide)))),
      targetCell 1 "2024-06-15" 15,
      targetCell 2 "2024-06-01" 1]
    let destination ← input? 2 [
      targetCell 1 "2024-06-10" 10,
      targetCell 2 "2024-06-11" 11,
      rootTargetCell "2024-06-20" 20]
    resultApplicationSummary? input destination [.malformed]) = some {
      values := [
        (address target.id 1, "2024-06-15"),
        (address target.id 2, "2024-06-16")]
      changes := [(address target.id 2, "2024-06-16")]
      errors := []
      cleared := []
      residual := [.malformed]
      row1 := .presentValue ⟨"2024-06-10", by decide⟩
      row2 := .presentValue ⟨"2024-06-16", by decide⟩
      unrelated := .presentValue ⟨"2024-06-20", by decide⟩
    } := by
  native_decide

/- Row-local exhaustion and poison both become retained clears when their immutable source targets were filled, and they materialize exact absent destination states without claiming row topology. -/
example : (do
    let input ← input? 2 [
      sourceCell 2 "bad" (.rejected .dateFormat),
      targetCell 1 "2024-06-05" 5,
      targetCell 2 "2024-06-06" 6]
    let destination ← input? 2 [rootTargetCell "2024-06-20" 20]
    resultApplicationSummary? input destination) = some {
      values := []
      changes := []
      errors := []
      cleared := [address target.id 1, address target.id 2]
      residual := []
      row1 := .presentEmpty
      row2 := .presentEmpty
      unrelated := .presentValue ⟨"2024-06-20", by decide⟩
    } := by
  native_decide

/- A root source is read once at its own address and reaches every physical target row. -/
example :
    outerOperation?.isSome = true ∧
    outerOutcomes? 2 [
      outerCell "2024-06-15T00:30:00"
        (.parsed (.temporal (momentAt 15 0 30 |>.get (by native_decide))))
    ] = some [
      ({ field := outerSource.id, path := [] }, address target.id 1, accepted "2024-06-15"),
      ({ field := outerSource.id, path := [] }, address target.id 2, accepted "2024-06-15")
    ] := by
  native_decide

/- A formal root failure poisons every reached row while retaining the one root source address. -/
example :
    outerOutcomes? 2 [outerCell "bad" (.rejected .dateFormat)] = some [
      ({ field := outerSource.id, path := [] }, address target.id 1, .poison .dateFormat),
      ({ field := outerSource.id, path := [] }, address target.id 2, .poison .dateFormat)
    ] := by
  native_decide

private def nestedSource : FlatFieldDecl := {
  source with id := 11, name := "MilestoneStamp", groupPath := ["Project", "Milestones"], repeatableScope := [10] }

private def nestedTarget : FlatFieldDecl := {
  target with id := 12, name := "TaskDate", groupPath := ["Project", "Milestones", "Tasks"], repeatableScope := [10, 20] }

private def nestedModel : FlatModel := {
  fields := [nestedSource, nestedTarget]
  timeZoneId := "Europe/Berlin"
  repeatableGroups := [
    { level := 10, path := ["Project", "Milestones"], repeatability := some 5 },
    { level := 20, path := ["Project", "Milestones", "Tasks"],
      repeatability := some 5 }]
}

private def nestedPrepared :
    PreparedFlatStringContext nestedModel builtinStringPatternCompiler :=
  (prepareFlatStringContext { now := { epochMillis := 0 } }
    builtinStringPatternCompiler nestedModel).toOption.get (by native_decide)

private def nestedOperation? : Option (CheckedAddressedDateFromDateTime nestedModel) :=
  (checkAddressedDateFromDateTime nestedModel ["Project", "Milestones", "Tasks"]
    nestedTarget.id (parent "MilestoneStamp")).toOption

private def nestedSourceCell (outer : Nat) (stored : String)
    (raw : RawCell) : ClassifiedCellInput :=
  { address := { field := nestedSource.id, path := [outer] }, stored, raw }

private def nestedOutcomes? (rows : List RowAddr)
    (cells : List ClassifiedCellInput) :
    Option (List (CellAddr × CellAddr × FullDateTargetOutcome)) := do
  let operation ← nestedOperation?
  let input ← (checkDocument nestedPrepared "en_US" {
    instantiatedRows := rows, cells }).toOption
  let outcomes ← (operation.execute input).toOption
  pure (outcomes.map fun entry => (entry.sourceField, entry.targetField, entry.outcome))

private def nestedRows : List RowAddr :=
  [{ group := 10, path := [1] }, { group := 10, path := [2] },
    { group := 20, path := [1, 1] }, { group := 20, path := [1, 2] },
    { group := 20, path := [2, 1] }, { group := 20, path := [2, 2] }]

private def nestedSourceAddress (outer : Nat) : CellAddr :=
  { field := nestedSource.id, path := [outer] }

private def nestedTargetAddress (outer inner : Nat) : CellAddr :=
  { field := nestedTarget.id, path := [outer, inner] }

/- Two distinct enclosing values separate own-row correlation from reading the first source globally
or borrowing the leaf path for a middle-level source. -/
example :
    nestedOperation?.isSome = true ∧
    nestedOutcomes? nestedRows [
      nestedSourceCell 1 "2024-06-15T00:30:00"
        (.parsed (.temporal (momentAt 15 0 30 |>.get (by native_decide)))),
      nestedSourceCell 2 "2024-06-16T23:45:00"
        (.parsed (.temporal (momentAt 16 23 45 |>.get (by native_decide))))
    ] = some [
      (nestedSourceAddress 1, nestedTargetAddress 1 1, accepted "2024-06-15"),
      (nestedSourceAddress 1, nestedTargetAddress 1 2, accepted "2024-06-15"),
      (nestedSourceAddress 2, nestedTargetAddress 2 1, accepted "2024-06-16"),
      (nestedSourceAddress 2, nestedTargetAddress 2 2, accepted "2024-06-16")
    ] := by
  native_decide

/- A malformed enclosing source poisons only its own leaves; the sibling enclosing row still
computes both values. -/
example :
    nestedOutcomes? nestedRows [
      nestedSourceCell 1 "bad" (.rejected .dateFormat),
      nestedSourceCell 2 "2024-06-16T23:45:00"
        (.parsed (.temporal (momentAt 16 23 45 |>.get (by native_decide))))
    ] = some [
      (nestedSourceAddress 1, nestedTargetAddress 1 1, .poison .dateFormat),
      (nestedSourceAddress 1, nestedTargetAddress 1 2, .poison .dateFormat),
      (nestedSourceAddress 2, nestedTargetAddress 2 1, accepted "2024-06-16"),
      (nestedSourceAddress 2, nestedTargetAddress 2 2, accepted "2024-06-16")
    ] := by
  native_decide

/- Clean absence follows the same enclosing-row boundary without becoming poison. -/
example :
    nestedOutcomes? nestedRows [
      nestedSourceCell 2 "2024-06-16T23:45:00"
        (.parsed (.temporal (momentAt 16 23 45 |>.get (by native_decide))))
    ] = some [
      (nestedSourceAddress 1, nestedTargetAddress 1 1, .noValue),
      (nestedSourceAddress 1, nestedTargetAddress 1 2, .noValue),
      (nestedSourceAddress 2, nestedTargetAddress 2 1, accepted "2024-06-16"),
      (nestedSourceAddress 2, nestedTargetAddress 2 2, accepted "2024-06-16")
    ] := by
  native_decide

/- An enclosing row with no physical leaves creates no implicit target outcomes. -/
example :
    nestedOutcomes?
      [{ group := 10, path := [1] }, { group := 10, path := [2] },
        { group := 20, path := [2, 1] }, { group := 20, path := [2, 2] }]
      [nestedSourceCell 1 "2024-06-15T00:30:00"
          (.parsed (.temporal (momentAt 15 0 30 |>.get (by native_decide)))),
        nestedSourceCell 2 "2024-06-16T23:45:00"
          (.parsed (.temporal (momentAt 16 23 45 |>.get (by native_decide))))] = some [
      (nestedSourceAddress 2, nestedTargetAddress 2 1, accepted "2024-06-16"),
      (nestedSourceAddress 2, nestedTargetAddress 2 2, accepted "2024-06-16")
    ] := by
  native_decide

private def thirdLevelSource : FlatFieldDecl := {
  source with id := 21, name := "MilestoneStamp", groupPath := ["Project", "Milestones"], repeatableScope := [10] }

private def thirdLevelTarget : FlatFieldDecl := {
  target with id := 22, name := "SubtaskDate", groupPath := ["Project", "Milestones", "Tasks", "Subtasks"], repeatableScope := [10, 20, 30] }

private def thirdLevelModel : FlatModel := {
  fields := [thirdLevelSource, thirdLevelTarget]
  timeZoneId := "Europe/Berlin"
  repeatableGroups := [
    { level := 10, path := ["Project", "Milestones"], repeatability := some 5 },
    { level := 20, path := ["Project", "Milestones", "Tasks"],
      repeatability := some 5 },
    { level := 30, path := ["Project", "Milestones", "Tasks", "Subtasks"],
      repeatability := some 5 }]
}

private def thirdLevelPrepared :
    PreparedFlatStringContext thirdLevelModel builtinStringPatternCompiler :=
  (prepareFlatStringContext { now := { epochMillis := 0 } }
    builtinStringPatternCompiler thirdLevelModel).toOption.get (by native_decide)

private def thirdLevelOperation? :
    Option (CheckedAddressedDateFromDateTime thirdLevelModel) :=
  (checkAddressedDateFromDateTime thirdLevelModel
    ["Project", "Milestones", "Tasks", "Subtasks"] thirdLevelTarget.id {
      base := .absolute, groups := ["Project", "Milestones"]
      field := "MilestoneStamp"
    }).toOption

private def thirdLevelSourceCell (outer : Nat) (stored : String)
    (raw : RawCell) : ClassifiedCellInput :=
  { address := { field := thirdLevelSource.id, path := [outer] }, stored, raw }

private def thirdLevelOutcomes? (rows : List RowAddr)
    (cells : List ClassifiedCellInput) :
    Option (List (CellAddr × CellAddr × FullDateTargetOutcome)) := do
  let operation ← thirdLevelOperation?
  let input ← (checkDocument thirdLevelPrepared "en_US" {
    instantiatedRows := rows, cells }).toOption
  let outcomes ← operation.execute input |>.toOption
  pure (outcomes.map fun entry =>
    (entry.sourceField, entry.targetField, entry.outcome))

private def thirdLevelRows : List RowAddr :=
  [{ group := 10, path := [1] }, { group := 10, path := [2] },
    { group := 20, path := [1, 1] }, { group := 20, path := [1, 2] },
    { group := 20, path := [2, 1] },
    { group := 30, path := [1, 1, 1] }, { group := 30, path := [1, 1, 2] },
    { group := 30, path := [1, 2, 1] }, { group := 30, path := [2, 1, 1] }]

private def thirdLevelSourceAddress (outer : Nat) : CellAddr :=
  { field := thirdLevelSource.id, path := [outer] }

private def thirdLevelTargetAddress (outer middle inner : Nat) : CellAddr :=
  { field := thirdLevelTarget.id, path := [outer, middle, inner] }

/- A source two axes above the target keeps its own outer address while each physical leaf retains all three coordinates. -/
example : thirdLevelOperation?.isSome = true ∧
    thirdLevelOutcomes? thirdLevelRows [
      thirdLevelSourceCell 1 "2024-06-15T00:30:00"
        (.parsed (.temporal (momentAt 15 0 30 |>.get (by native_decide)))),
      thirdLevelSourceCell 2 "2024-06-16T23:45:00"
        (.parsed (.temporal (momentAt 16 23 45 |>.get (by native_decide))))
    ] = some [
      (thirdLevelSourceAddress 1, thirdLevelTargetAddress 1 1 1,
        accepted "2024-06-15"),
      (thirdLevelSourceAddress 1, thirdLevelTargetAddress 1 1 2,
        accepted "2024-06-15"),
      (thirdLevelSourceAddress 1, thirdLevelTargetAddress 1 2 1,
        accepted "2024-06-15"),
      (thirdLevelSourceAddress 2, thirdLevelTargetAddress 2 1 1,
        accepted "2024-06-16")
    ] := by
  native_decide

/- A malformed outer source poisons only its descendant leaves across two deeper axes. -/
example : thirdLevelOutcomes? thirdLevelRows [
    thirdLevelSourceCell 1 "bad" (.rejected .dateFormat),
    thirdLevelSourceCell 2 "2024-06-16T23:45:00"
      (.parsed (.temporal (momentAt 16 23 45 |>.get (by native_decide))))
  ] = some [
    (thirdLevelSourceAddress 1, thirdLevelTargetAddress 1 1 1,
      .poison .dateFormat),
    (thirdLevelSourceAddress 1, thirdLevelTargetAddress 1 1 2,
      .poison .dateFormat),
    (thirdLevelSourceAddress 1, thirdLevelTargetAddress 1 2 1,
      .poison .dateFormat),
    (thirdLevelSourceAddress 2, thirdLevelTargetAddress 2 1 1,
      accepted "2024-06-16")
  ] := by
  native_decide

/- Ancestor rows without a physical third-level target row produce no implicit outcomes. -/
example : thirdLevelOutcomes?
    [{ group := 10, path := [1] }, { group := 10, path := [2] },
      { group := 20, path := [1, 1] }, { group := 20, path := [2, 1] },
      { group := 30, path := [2, 1, 1] }]
    [thirdLevelSourceCell 1 "2024-06-15T00:30:00"
      (.parsed (.temporal (momentAt 15 0 30 |>.get (by native_decide)))),
    thirdLevelSourceCell 2 "2024-06-16T23:45:00"
      (.parsed (.temporal (momentAt 16 23 45 |>.get (by native_decide))))] = some [
      (thirdLevelSourceAddress 2, thirdLevelTargetAddress 2 1 1,
        accepted "2024-06-16")
    ] := by
  native_decide

end A12Kernel.Conformance.AddressedDateFromDateTime
