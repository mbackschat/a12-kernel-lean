import A12Kernel.Elaboration.AddressedDateFromDateTime

/-! # Repeatable `DateFromDateTime` locks

One same-group DateTime source computes one full-Date target per physically instantiated row. The cases retain both exact addresses and separate clean absence from row-local formal poison. -/

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

private def model : FlatModel := {
  fields := [source, target, rootTarget]
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

private def operation? : Option (CheckedAddressedDateFromDateTime model) :=
  (checkAddressedDateFromDateTime model ["Schedule", "Slots"] target.id
    (bare "SlotStamp")).toOption

private def momentAt (day hour minute : Nat) : Option TemporalValue := do
  let wall ← LocalDateTime.ofYmdHms? 2024 6 day hour minute 0
  let instant ← ModelZone.ConcreteProfile.europeBerlin.resolveLocal? wall
  pure (.dateTime instant wall.date.civil.parts wall.time .storedGregorian)

private def sourceCell (row : Nat) (stored : String) (raw : RawCell) : ClassifiedCellInput :=
  { address := { field := source.id, path := [row] }, stored, raw }

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

end A12Kernel.Conformance.AddressedDateFromDateTime
