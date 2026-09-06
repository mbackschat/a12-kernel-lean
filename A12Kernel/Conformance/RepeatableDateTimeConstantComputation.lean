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

/-- A **DATE** declaration carrying the DateTime format string. The family gate reads the declared
format and not the field's kind, and this cell is now measured on both halves — admitted, and storing
through that format ([checkpoint](../../docs/SOURCES.md#src-datetime-carrier-stores-by-its-format)) —
so this carrier admits it. Its components are complete, which the certificate still requires. -/
private def dateTimeShapedDate := temporalField 2 "D" .date TemporalComponents.now
  ["Probe", "Rows"] [10] "yyyy-MM-dd'T'HH:mm:ss"

/-- The **components** control beside it: a DATE declaration at the same DateTime format string but
naming only a calendar date's components. It must stay refused, because otherwise the row above would
read as "the kind gate is gone" when what it shows is that the kind gate was never the operative one.
Yesterday's Date sibling passed for exactly that wrong reason. -/
private def partialDateAtDateTimeFormat :=
  temporalField 4 "P" .date TemporalComponents.fullDate
    ["Probe", "Rows"] [10] "yyyy-MM-dd'T'HH:mm:ss"

private def fixedStamp := temporalField 3 "Fixed" .dateTime TemporalComponents.now
  ["Probe", "Store"] [] "yyyy-MM-dd'T'HH:mm:ss"

/-- Europe/Berlin rather than UTC, so the model has a spring-forward discontinuity for the gap case
below to land in. -/
private def model : FlatModel := {
  fields := [stamp, dateTimeShapedDate, fixedStamp, partialDateAtDateTimeFormat]
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

/- **The cross-kind target, and what still refuses beside it.** A DATE declaration carrying the
   DateTime format string is admitted, because the family gate reads the format; the same kind at the
   same format but with a calendar-date component set is refused, and so is the nonrepeatable target
   the shared placement certificate declines. The middle row is the one that keeps the first honest:
   without it, admitting the first would be indistinguishable from having no gate at this position at
   all. The two refusals separate by class: the component-set one draws the shared literal-comparison ladder's
   temporal class, while the placement decline is this project's own routing and claims none. -/
example : ([dateTimeShapedDate.id, partialDateAtDateTimeFormat.id,
      fixedStamp.id].map fun target =>
      match checkRepeatableDateTimeConstantComputation model ["Probe"] target marchFifth with
      | .error cause => (false, cause.diagnostic?)
      | .ok _ => (true, none)) =
    [(true, none), (false, some .invalidCompareToDate), (false, none)] := by
  native_decide

/- And it **stores through its declared format**, which is the half that was missing when this
   certificate stayed narrowed: the DATE-declared field renders the same text its DATETIME sibling
   does, as measured. -/
example : outcome? ["Probe"] dateTimeShapedDate.id =
    some (.accepted (stored "2024-03-05T12:30:00")) := by
  native_decide

end A12Kernel.Conformance.RepeatableDateTimeConstantComputation
