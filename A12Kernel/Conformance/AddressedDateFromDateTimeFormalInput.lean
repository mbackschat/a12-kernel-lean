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

end A12Kernel.Conformance.AddressedDateFromDateTimeFormalInput
