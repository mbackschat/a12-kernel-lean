import A12Kernel.Elaboration.AddressedTimeFromDateTime

/-! # Checked repeatable `TimeFromDateTime` placement locks -/

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

/- Target ownership, target repetition, complete-DateTime admission, and source-scope binding are four distinct addressed gates. -/
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

end A12Kernel.Conformance.AddressedTimeFromDateTime
