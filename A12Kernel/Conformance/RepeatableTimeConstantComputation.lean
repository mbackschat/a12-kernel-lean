import A12Kernel.Elaboration.RepeatableTimeConstantComputation
import A12Kernel.Elaboration.CheckedDocument

/-! # Repeatable Time constant locks

The Kernel rows behind these cases are the [cross-group carrier](../../docs/SOURCES.md#src-cross-group-repeatable-constant-target)
and the [literal-family gate](../../docs/SOURCES.md#src-constant-literal-family-gate) checkpoints.
-/

namespace A12Kernel.Conformance.RepeatableTimeConstantComputation

open A12Kernel

private def temporalField (id : FieldId) (name : String) (kind : TemporalKind)
    (components : TemporalComponents) (groupPath : GroupPath)
    (scope : List RepeatableLevel) (format : String) : FlatFieldDecl := {
  id, name, groupPath, repeatableScope := scope
  policy := { kind := .temporal kind components }
  temporalTargetPolicy := some { format, partialMode := .full }
}

private def clock := temporalField 1 "T" .time TemporalComponents.time
  ["Probe", "Rows"] [10] "HH:mm:ss"

/-- A TIME declaration the Kernel refuses this constant for, because its declared format is
date-shaped: it takes a date literal instead. -/
private def dateShapedTime := temporalField 2 "T2" .time TemporalComponents.time
  ["Probe", "Rows"] [10] "yyyy-MM-dd"

/-- A **DATE** declaration whose clock format the Kernel admits this constant for, storing
`12:30:00`. This carrier declines it, which is the stated exclusion below. -/
private def clockShapedDate := temporalField 3 "DClock" .date TemporalComponents.fullDate
  ["Probe", "Rows"] [10] "HH:mm:ss"

private def fixedClock := temporalField 4 "Fixed" .time TemporalComponents.time
  ["Probe", "Store"] [] "HH:mm:ss"

private def model : FlatModel := {
  fields := [clock, dateShapedTime, clockShapedDate, fixedClock]
  repeatableGroups := [
    { level := 10, path := ["Probe", "Rows"], repeatability := some 3 }]
  timeZoneId := "UTC"
}

private def prepared : PreparedFlatStringContext model builtinStringPatternCompiler :=
  (prepareFlatStringContext { now := { epochMillis := 0 } }
    builtinStringPatternCompiler model).toOption.get (by native_decide)

private def rows (count : Nat) : Option (CheckedDocument model) :=
  (checkDocument prepared "en_US" {
    instantiatedRows :=
      (List.range count).map fun index => { group := 10, path := [index + 1] }
    cells := [] }).toOption

private def halfPastTwelve : TimeOfDay :=
  (TimeOfDay.ofHms? 12 30 0).get (by native_decide)

private def outcome? (declaringGroup : GroupPath) (target : FieldId) :
    Option TimeTargetOutcome :=
  (checkRepeatableTimeConstantComputation model declaringGroup target
    halfPastTwelve).toOption.map (·.outcome)

private def outcomes? (declaringGroup : GroupPath) (target : FieldId) (count : Nat) :
    Option (List RepeatableTimeConstantComputationOutcome) :=
  (checkRepeatableTimeConstantComputation model declaringGroup target
    halfPastTwelve).toOption.bind fun operation =>
      (rows count).bind fun input => (operation.execute input).toOption

private def stored (text : String) (nonempty : text ≠ "" := by decide) : StoredTime :=
  { text, nonempty }

/- The clock renders zero-padded through the declared format, and every admitted clock is accepted:
   this family owns no rejection branch, which is what the Kernel rows show by never erroring. -/
example : outcome? ["Probe"] clock.id = some (.accepted (stored "12:30:00")) := by
  native_decide

/- The constant reaches every physical target row and no more, from an ancestor exactly as from the
   target's own group. Two rows, two outcomes; no rows, none at all. -/
example : (outcomes? ["Probe"] clock.id 2, outcomes? ["Probe", "Rows"] clock.id 2,
    outcomes? ["Probe"] clock.id 0) =
    (some [{ targetField := { field := clock.id, path := [1] }
             outcome := .accepted (stored "12:30:00") },
           { targetField := { field := clock.id, path := [2] }
             outcome := .accepted (stored "12:30:00") }],
     some [{ targetField := { field := clock.id, path := [1] }
             outcome := .accepted (stored "12:30:00") },
           { targetField := { field := clock.id, path := [2] }
             outcome := .accepted (stored "12:30:00") }],
     some []) := by
  native_decide

/- **The two cross-kind cells, and the one place this carrier is narrower than the Kernel.** A TIME
   declaration whose format is date-shaped refuses the clock constant here and in the Kernel alike,
   so that decline is correct. A **DATE** declaration whose format is `HH:mm:ss` is the opposite: the
   Kernel admits it and stores `12:30:00`, while this carrier declines it because the shared
   `CheckedTimeTarget` also requires `kind = .time`. That is a stated exclusion, not a measured gate,
   so neither decline claims a Kernel class — the second one would be claiming the Kernel refuses a
   shape it accepts. -/
example : ((outcome? ["Probe"] dateShapedTime.id, outcome? ["Probe"] clockShapedDate.id),
    [dateShapedTime.id, clockShapedDate.id].map fun target =>
      match checkRepeatableTimeConstantComputation model ["Probe"] target halfPastTwelve with
      | .error cause => cause.diagnostic?.isSome
      | .ok _ => true) =
    ((none, none), [false, false]) := by
  native_decide

/- Placement is containment: the target's own group and every ancestor admit it, and only a group the
   target does not lie below is refused — with the Kernel identity that refusal actually carries. -/
example : ([["Probe", "Rows"], ["Probe"]].map fun group =>
      (checkRepeatableTimeConstantComputation model group clock.id
        halfPastTwelve).toOption.isSome,
    match checkRepeatableTimeConstantComputation model ["Probe", "Store"] clock.id
        halfPastTwelve with
    | .error cause => cause.diagnostic?.map KernelStaticDiagnostic.kernelCode
    | .ok _ => none) =
    ([true, true], some "MVK_ERROR_FIELD_NOT_IN_RULEGROUP") := by
  native_decide

/- A nonrepeatable target belongs to no carrier here and is declined by the shared certificate rather
   than by a second local gate, so it claims no Kernel class. -/
example : (match checkRepeatableTimeConstantComputation model ["Probe"] fixedClock.id
      halfPastTwelve with
    | .error cause => (cause.diagnostic?.isSome, true)
    | .ok _ => (false, false)) = (false, true) := by
  native_decide

end A12Kernel.Conformance.RepeatableTimeConstantComputation
