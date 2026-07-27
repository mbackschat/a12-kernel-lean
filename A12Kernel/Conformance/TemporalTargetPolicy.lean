import A12Kernel.Elaboration.TemporalTargetPolicy

/-! # Checked temporal-target policy locks -/

namespace A12Kernel.Conformance.TemporalTargetPolicy

open A12Kernel

private def fullDate : TemporalComponents := TemporalComponents.fullDate

private def temporalTarget
    (id : FieldId) (name format : String)
    (kind : TemporalKind) (components : TemporalComponents)
    (partialMode : TemporalPartialMode := .full)
    (youngerThan1900Check : Bool := false) : FlatFieldDecl := {
  id
  groupPath := ["Order"]
  name
  policy := { kind := .temporal kind components }
  temporalTargetPolicy := some {
    format
    partialMode
    youngerThan1900Check } }

private def checkedPolicyOf
    (model : FlatModel) (target : FieldId) :
    Option (TemporalTargetPolicy × String) :=
  match elaborateTemporalTargetPolicy model target with
  | .ok checked => some (checked.policy, checked.timeZoneId)
  | .error _ => none

private def errorOf
    (result : Except TemporalTargetElabError value) :
    Option TemporalTargetElabError :=
  match result with
  | .ok _ => none
  | .error error => some error

/- The checked target exposes the exact declaration policy and the same model's zone. -/
example :
    let target := temporalTarget 0 "Date" "dd.MM.yyyy"
      .date fullDate .yearOptional true
    let model : FlatModel := {
      fields := [target]
      timeZoneId := "Europe/Berlin" }
    checkedPolicyOf model 0 =
        some ({
          format := "dd.MM.yyyy"
          partialMode := .yearOptional
          youngerThan1900Check := true },
          "Europe/Berlin") := by
  native_decide

/- A non-temporal target reaches a distinct shape error without target policy. -/
example :
    let target : FlatFieldDecl := {
      id := 0
      groupPath := ["Order"]
      name := "Amount"
      policy := { kind := .number { scale := 0, signed := true } } }
    errorOf (elaborateTemporalTargetPolicy { fields := [target] } 0) =
      some (.targetNotTemporal 0) := by
  native_decide

/- Time metadata is coherent but outside this first Date/DateTime target boundary. -/
example :
    let time : TemporalComponents :=
      { year := false, month := false, day := false,
        hour := true, minute := true, second := true }
    let target := temporalTarget 0 "Time" "HH:mm:ss" .time time
    errorOf (elaborateTemporalTargetPolicy { fields := [target] } 0) =
      some (.unsupportedTargetKind 0 .time) := by
  native_decide

/- Missing declaration policy is explicit insufficient information, never a guessed canonical format. -/
example :
    let target : FlatFieldDecl := {
      id := 0
      groupPath := ["Order"]
      name := "Date"
      policy := { kind := .temporal .date fullDate } }
    errorOf (elaborateTemporalTargetPolicy { fields := [target] } 0) =
      some (.targetPolicyUnavailable 0) := by
  native_decide

end A12Kernel.Conformance.TemporalTargetPolicy
