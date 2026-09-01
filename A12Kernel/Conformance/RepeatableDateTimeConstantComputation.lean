import A12Kernel.Elaboration.RepeatableDateTimeConstantComputation
import A12Kernel.Elaboration.CheckedDocument

/-! # Repeatable DateTime constant locks

The Kernel rows behind the placement and admission cases are the [cross-group carrier](../../docs/SOURCES.md#src-cross-group-repeatable-constant-target)
and [literal-composition](../../docs/SOURCES.md#src-temporal-constant-literal-composition) checkpoints.
The [zone-split checkpoint](../../docs/SOURCES.md#src-datetime-constant-zone-split) additionally fixes
the stored text and the model-zone gap refusal on this exact carrier.
-/

namespace A12Kernel.Conformance.RepeatableDateTimeConstantComputation

open A12Kernel

private def temporalField (id : FieldId) (name : String) (kind : TemporalKind)
    (components : TemporalComponents) (groupPath : GroupPath)
    (scope : List RepeatableLevel) (format : String) : FlatFieldDecl := {
  id, name, groupPath, repeatableScope := scope
  policy := { kind := .temporal kind components }
  temporalTargetPolicy := some { format, partialMode := .full }
}

private def stamp := temporalField 1 "S" .dateTime TemporalComponents.now
  ["Probe", "Rows"] [10] "yyyy-MM-dd'T'HH:mm:ss"

/-- A **DATE** declaration carrying the DateTime format string. The measured family gate reads the
declared format and not the field's kind, so the Kernel's treatment of this cell is unmeasured; this
carrier declines it through the shared certificate's `kind = .dateTime` requirement. -/
private def dateTimeShapedDate := temporalField 2 "D" .date TemporalComponents.fullDate
  ["Probe", "Rows"] [10] "yyyy-MM-dd'T'HH:mm:ss"

private def fixedStamp := temporalField 3 "Fixed" .dateTime TemporalComponents.now
  ["Probe", "Store"] [] "yyyy-MM-dd'T'HH:mm:ss"

/-- Europe/Berlin rather than UTC, so the model has a spring-forward discontinuity for the gap case
below to land in. -/
private def model : FlatModel := {
  fields := [stamp, dateTimeShapedDate, fixedStamp]
  repeatableGroups := [
    { level := 10, path := ["Probe", "Rows"], repeatability := some 3 }]
  timeZoneId := "Europe/Berlin"
}

private def prepared : PreparedFlatStringContext model builtinStringPatternCompiler :=
  (prepareFlatStringContext { now := { epochMillis := 0 } }
    builtinStringPatternCompiler model).toOption.get (by native_decide)

private def rows (count : Nat) : Option (CheckedDocument model) :=
  (checkDocument prepared "en_US" {
    instantiatedRows :=
      (List.range count).map fun index => { group := 10, path := [index + 1] }
    cells := [] }).toOption

/-- The measured admitted literal `"05.03.2024T12:30:00"`, already classified. -/
private def marchFifth : LocalDateTime :=
  (LocalDateTime.ofYmdHms? 2024 3 5 12 30 0).get (by native_decide)

/-- 02:30 on the Berlin spring-forward night: a wall label naming no instant at all. -/
private def gapLabel : LocalDateTime :=
  (LocalDateTime.ofYmdHms? 2024 3 31 2 30 0).get (by native_decide)

private def run? (declaringGroup : GroupPath) (target : FieldId) (count : Nat)
    (constant : LocalDateTime := marchFifth) :
    Option RepeatableDateTimeConstantComputationRun :=
  (checkRepeatableDateTimeConstantComputation model declaringGroup target
    constant).toOption.bind fun operation =>
      (rows count).bind fun input => (operation.execute input).toOption

private def outcome? (declaringGroup : GroupPath) (target : FieldId)
    (constant : LocalDateTime := marchFifth) : Option DateTimeTargetOutcome :=
  (run? declaringGroup target 1 constant).bind fun run =>
    run.outcomes.head?.map fun entry => entry.outcome

private def outcomes? (declaringGroup : GroupPath) (target : FieldId) (count : Nat) :
    Option (List RepeatableDateTimeConstantComputationOutcome) :=
  (run? declaringGroup target count).map (·.outcomes)

private def stored (text : String) (nonempty : text ≠ "" := by decide) : StoredDateTime :=
  { text, nonempty }

/- **The literal's spelling and the target's format differ, and the target's format wins.** The Kernel
   admits the day-first `"05.03.2024T12:30:00"` into this `yyyy-MM-dd'T'HH:mm:ss` target and stores
   exactly this ISO text on both codegen strategies. -/
example : outcome? ["Probe"] stamp.id = some (.accepted (stored "2024-03-05T12:30:00")) := by
  native_decide

/- The constant reaches every physical target row and no more, from an ancestor exactly as from the
   target's own group. Two rows, two outcomes; no rows, none at all. -/
example : (outcomes? ["Probe"] stamp.id 2, outcomes? ["Probe", "Rows"] stamp.id 2,
    outcomes? ["Probe"] stamp.id 0) =
    (some [{ targetField := { field := stamp.id, path := [1] }
             outcome := .accepted (stored "2024-03-05T12:30:00") },
           { targetField := { field := stamp.id, path := [2] }
             outcome := .accepted (stored "2024-03-05T12:30:00") }],
     some [{ targetField := { field := stamp.id, path := [1] }
             outcome := .accepted (stored "2024-03-05T12:30:00") },
           { targetField := { field := stamp.id, path := [2] }
             outcome := .accepted (stored "2024-03-05T12:30:00") }],
     some []) := by
  native_decide

/- Successful rows populate no residual channel. -/
example : (run? ["Probe"] stamp.id 2).map (·.formalErrorsInOperands) = some [] := by
  native_decide

/- The inherited capacity branch is retained on this result shape: the first three rows store, the
   fourth clears, and no residual is manufactured. -/
example : (run? ["Probe"] stamp.id 4).map (fun run =>
    (run.outcomes,
      run.formalErrorsInOperands)) =
    some ([
      { targetField := { field := stamp.id, path := [1] }
        outcome := .accepted (stored "2024-03-05T12:30:00") },
      { targetField := { field := stamp.id, path := [2] }
        outcome := .accepted (stored "2024-03-05T12:30:00") },
      { targetField := { field := stamp.id, path := [3] }
        outcome := .accepted (stored "2024-03-05T12:30:00") },
      { targetField := { field := stamp.id, path := [4] }
        outcome := .noValue }], []) := by
  native_decide

/- A spring-forward gap label produces no computed outcome in the model zone. -/
example : (outcome? ["Probe"] stamp.id gapLabel,
    (ModelZone.ConcreteProfile.resolveLocal? .europeBerlin gapLabel).isSome) =
    (none, false) := by
  native_decide

/- The failure is retained once per in-capacity target row in the API-named residual channel, even
   though a constant has no operands. It is not a poison outcome or a clear. -/
example : (run? ["Probe"] stamp.id 2 gapLabel).map (fun run =>
    (run.outcomes,
      run.formalErrorsInOperands.map fun finding =>
        (finding.targetField, finding.errorCode))) =
    some ([], [({ field := stamp.id, path := [1] }, berechnungsWertFehler),
      ({ field := stamp.id, path := [2] }, berechnungsWertFehler)]) := by
  native_decide

/- Placement is containment: the target's own group and every ancestor admit it, and only a group the
   target does not lie below is refused — with the Kernel identity that refusal actually carries. -/
example : ([["Probe", "Rows"], ["Probe"]].map fun group =>
      (checkRepeatableDateTimeConstantComputation model group stamp.id
        marchFifth).toOption.isSome,
    match checkRepeatableDateTimeConstantComputation model ["Probe", "Store"] stamp.id
        marchFifth with
    | .error cause => cause.diagnostic?.map KernelStaticDiagnostic.kernelCode
    | .ok _ => none) =
    ([true, true], some "MVK_ERROR_FIELD_NOT_IN_RULEGROUP") := by
  native_decide

/- **The stated exclusion.** A DATE declaration carrying this DateTime format string is declined here
   for its kind, and the nonrepeatable target is declined by the shared placement certificate. Neither
   decline claims a Kernel class: the measured gate reads the declared format rather than the kind, so
   asserting a refusal for the first would assert one the Kernel may well not make. -/
example : ([dateTimeShapedDate.id, fixedStamp.id].map fun target =>
      match checkRepeatableDateTimeConstantComputation model ["Probe"] target marchFifth with
      | .error cause => (false, cause.diagnostic?.isSome)
      | .ok _ => (true, false)) =
    [(false, false), (false, false)] := by
  native_decide

end A12Kernel.Conformance.RepeatableDateTimeConstantComputation
