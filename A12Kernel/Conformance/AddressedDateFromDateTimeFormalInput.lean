import A12Kernel.Elaboration.AddressedDateFromDateTimeFormalInput

/-! # Addressed `DateFromDateTime` formal-input locks -/

namespace A12Kernel.Conformance.AddressedDateFromDateTimeFormalInput

open A12Kernel

private def dateTimeField (id : FieldId) (name : String) : FlatFieldDecl := {
  id, name, groupPath := ["Schedule"], repeatableScope := []
  policy := { kind := .temporal .dateTime TemporalComponents.now }
  temporalTargetPolicy := some { format := "yyyy-MM-dd'T'HH:mm:ss" }
}

private def source := dateTimeField 1 "ScheduleStamp"
private def target : FlatFieldDecl := {
  id := 2
  name := "SlotDate"
  groupPath := ["Schedule", "Slots"]
  repeatableScope := [10]
  policy := { kind := .temporal .date TemporalComponents.fullDate }
  temporalTargetPolicy := some { format := "yyyy-MM-dd", partialMode := .full }
}
private def unrelated := dateTimeField 3 "Unrelated"

private def model : FlatModel := {
  fields := [source, target, unrelated]
  timeZoneId := "Europe/Berlin"
  repeatableGroups := [
    { level := 10, path := ["Schedule", "Slots"], repeatability := some 2 }
  ]
}

private def parent (field : String) : SurfaceFieldPath :=
  { base := .relative 1, groups := [], field }

private def operation? :=
  (checkAddressedDateFromDateTime model ["Schedule", "Slots"] target.id
    (parent source.name)).toOption

private def rejected (field : FieldId) (path : List Nat) : ClassifiedCellInput := {
  address := { field, path }
  stored := "bad"
  raw := .rejected .dateFormat
}

private def prepared : PreparedFlatStringContext model
    builtinStringPatternCompiler :=
  (prepareFlatStringContext { now := { epochMillis := 0 } }
    builtinStringPatternCompiler model).toOption.get (by native_decide)

private def input? : Option (CheckedDocument model) :=
  (checkDocument prepared "en_US" {
    instantiatedRows := [
      { group := 10, path := [1] },
      { group := 10, path := [2] }
    ]
    cells := [
      rejected source.id [],
      rejected target.id [1],
      rejected unrelated.id []
    ]
  }).toOption

/- Runtime reaches one root source from two target rows, but eager collection inventories its exact placement once and excludes target and unrelated findings. -/
example :
    (do
      let operation ← operation?
      let input ← input?
      let result ← operation.executeResultWithFormalInputs input |>.toOption
      let findings := result.fullDate.formalErrorsInOperands
      pure findings) = some [{
        address := { field := source.id, path := [] },
        cause := .dateFormat
      }] := by
  native_decide

private def indexedSource : FlatFieldDecl := {
  id := 11
  name := "SlotStamp"
  groupPath := ["Schedule", "Slots"]
  repeatableScope := [10]
  policy := { kind := .temporal .dateTime TemporalComponents.now }
  temporalTargetPolicy := some { format := "yyyy-MM-dd'T'HH:mm:ss" }
}

private def indexedTarget : FlatFieldDecl := {
  id := 12
  name := "SlotDate"
  groupPath := ["Schedule", "Slots"]
  repeatableScope := [10]
  policy := { kind := .temporal .date TemporalComponents.fullDate }
  temporalTargetPolicy := some { format := "yyyy-MM-dd", partialMode := .full }
}

private def indexedModel : FlatModel := {
  fields := [indexedSource, indexedTarget]
  timeZoneId := "Europe/Berlin"
  repeatableGroups := [{
    level := 10
    path := ["Schedule", "Slots"]
    repeatability := some 2
    indexField := some indexedSource.id
  }]
}

private def indexedPrepared : PreparedFlatStringContext indexedModel
    builtinStringPatternCompiler :=
  (prepareFlatStringContext { now := { epochMillis := 0 } }
    builtinStringPatternCompiler indexedModel).toOption.get (by native_decide)

private def clock : TimeOfDay :=
  ⟨0, 30, 0, by decide⟩

private def indexedSourceCell (row : Nat) : ClassifiedCellInput := {
  address := { field := indexedSource.id, path := [row] }
  stored := "2024-06-15T00:30:00"
  raw := .parsed (.temporal (.dateTime
    { epochMillis := 1718404200000 }
    { year := 2024, month := 6, day := 15 }
    clock .storedGregorian))
}

private def indexedTargetCell (row : Nat) : ClassifiedCellInput := {
  address := { field := indexedTarget.id, path := [row] }
  stored := "2024-06-01"
  raw := .parsed (.temporal (.date {
    instant := { epochMillis := 1717200000000 }
    parts := { year := 2024, month := 6, day := 1 }
    basis := .storedGregorian
  }))
}

private def indexedInput? : Option (CheckedDocument indexedModel) :=
  (checkDocument indexedPrepared "en_US" {
    instantiatedRows := [
      { group := 10, path := [1] },
      { group := 10, path := [2] }
    ]
    cells := [
      indexedSourceCell 1,
      indexedSourceCell 2,
      indexedTargetCell 1,
      indexedTargetCell 2
    ]
  }).toOption

private def indexedOperation? :
    Option (CheckedAddressedDateFromDateTime indexedModel) :=
  (checkAddressedDateFromDateTime indexedModel ["Schedule", "Slots"]
    indexedTarget.id { base := .relative 0, groups := [], field := indexedSource.name })
    |>.toOption

/- Duplicate DateTime indexes are both eager formal inputs and reached computation poison, so both source-filled FullDate targets clear. -/
example :
    (do
      let operation ← indexedOperation?
      let input ← indexedInput?
      let result ← operation.executeResultWithFormalInputs input |>.toOption
      pure (
        result.fullDate.formalErrorsInOperands,
        result.fullDate.withoutErrors.map (·.targetField),
        result.fullDate.withErrors.map (·.targetField),
        result.fullDate.cleared)) = some ([
          {
            address := { field := indexedSource.id, path := [1] }
            cause := .duplicateIndex
          },
          {
            address := { field := indexedSource.id, path := [2] }
            cause := .duplicateIndex
          }
        ], [], [], [
          { field := indexedTarget.id, path := [1] },
          { field := indexedTarget.id, path := [2] }
        ]) := by
  native_decide

end A12Kernel.Conformance.AddressedDateFromDateTimeFormalInput
