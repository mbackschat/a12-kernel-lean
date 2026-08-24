import A12Kernel.Elaboration.AddressedDateFromDateTime

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

end A12Kernel.Conformance.AddressedDateFromDateTime
