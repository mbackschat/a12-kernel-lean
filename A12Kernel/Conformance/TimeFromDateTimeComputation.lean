import A12Kernel.Elaboration.TimeFromDateTimeComputation

/-! # Checked scalar `TimeFromDateTime` computation locks -/

namespace A12Kernel.Conformance.TimeFromDateTimeComputation

open A12Kernel

private def source : FlatFieldDecl := {
  id := 1
  groupPath := ["Order"]
  name := "Moment"
  policy := { kind := .temporal .dateTime TemporalComponents.now }
  temporalTargetPolicy := some {
    format := "yyyy-MM-dd'T'HH:mm:ss"
    partialMode := .full
  }
}

private def target : FlatFieldDecl := {
  id := 2
  groupPath := ["Order"]
  name := "Clock"
  policy := { kind := .temporal .time TemporalComponents.time }
  temporalTargetPolicy := some { format := "HH:mm:ss", partialMode := .full }
}

private def other : FlatFieldDecl := {
  target with id := 3, name := "OtherClock"
}

/-- Two legal sources whose declared **kind** and declared **format** disagree, plus a DATE_TIME
    declared with a bare clock. A same-kind source cannot separate a kind test from a component
    test, so the conjunct these refute survived every other row here. -/
private def dateAsStamp : FlatFieldDecl :=
  { source with
    id := 4
    name := "DateAsStamp"
    policy := { kind := .temporal .date TemporalComponents.now } }

private def timeAsStamp : FlatFieldDecl :=
  { source with
    id := 5
    name := "TimeAsStamp"
    policy := { kind := .temporal .time TemporalComponents.now } }

private def stampAsClock : FlatFieldDecl :=
  { source with
    id := 6
    name := "StampAsClock"
    policy := { kind := .temporal .dateTime TemporalComponents.time } }

private def model : FlatModel := {
  fields := [source, target, other, dateAsStamp, timeAsStamp, stampAsClock]
  timeZoneId := "Europe/Berlin"
}

private def prepared :
    PreparedFlatStringContext model builtinStringPatternCompiler :=
  (prepareFlatStringContext { now := { epochMillis := 0 } }
    builtinStringPatternCompiler model).toOption.get (by native_decide)

private def operation? : Option (CheckedTimeFromDateTimeComputation model) :=
  (elaborateTimeFromDateTimeComputation model source.id target.id).toOption

private def clock (hour minute second : Nat)
    (valid : hour < 24 ∧ minute < 60 ∧ second < 60) : TimeOfDay :=
  ⟨hour, minute, second, valid⟩

private def moment : TemporalValue :=
  let wall := LocalDateTime.ofYmdHms? 2024 6 15 0 30 0 |>.get
    (by native_decide)
  let instant := ModelZone.ConcreteProfile.europeBerlin.resolveLocal? wall |>.get
    (by native_decide)
  .dateTime instant wall.date.civil.parts wall.time .storedGregorian

private def sourceCell (stored : String) (raw : RawCell) : ClassifiedCellInput := {
  address := { field := source.id, path := [] }
  stored
  raw
}

private def timeCell (field : FieldId) (stored : String)
    (value : TimeOfDay) : ClassifiedCellInput := {
  address := { field, path := [] }
  stored
  raw := .parsed (.temporal (.time { epochMillis := 0 } value))
}

private def input? (cells : List ClassifiedCellInput) :
    Option (CheckedDocument model) :=
  (checkDocument prepared "en_US" {
    instantiatedRows := []
    cells
  }).toOption

private def outcome? (cells : List ClassifiedCellInput) :
    Option TimeTargetOutcome := do
  let operation ← operation?
  let input ← input? cells
  operation.evaluateOutcome input |>.toOption

private structure ResultSummary where
  values : List String
  changes : List String
  cleared : List FieldId
  residual : List FormalCause
  deriving Repr, DecidableEq

private def resultSummary? (cells : List ClassifiedCellInput)
    (residual : List FormalCause := []) : Option ResultSummary := do
  let operation ← operation?
  let input ← input? cells
  let view ← operation.executeResult input residual |>.toOption
  pure {
    values := view.withoutErrors.map (·.value.text)
    changes := view.withChanges.map (·.value.text)
    cleared := view.cleared
    residual := view.formalErrorsInOperands
  }

private def appliedStates? (sourceCells destinationCells :
    List ClassifiedCellInput) : Option (TimeTargetState × TimeTargetState) := do
  let operation ← operation?
  let input ← input? sourceCells
  let destination ← input? destinationCells
  let view ← operation.executeResult input ([] : List FormalCause) |>.toOption
  let applied ← view.applyToChecked destination |>.toOption
  pure (applied target.id, applied other.id)

private def extracted : StoredTime := ⟨"00:30:00", by decide⟩

private def oldTarget : TimeOfDay := clock 0 30 0 (by decide)

private def differentTarget : TimeOfDay := clock 7 15 0 (by decide)

private def unrelatedTarget : TimeOfDay := clock 8 45 0 (by decide)

/- The standalone source-to-target carrier is admitted and extracts the retained Berlin wall clock, not the UTC clock of the source instant. -/
example : operation?.isSome = true ∧
    outcome? [sourceCell "2024-06-15T00:30:00"
      (.parsed (.temporal moment))] = some (.accepted extracted) := by
  native_decide

/- The source gate reads the declared **format**'s completeness and never the declared kind,
Kernel-calibrated on both codegen strategies at the [difference-gate checkpoint](../../docs/sources/computation-placement-and-constant-probes.md#src-temporal-difference-gates-read-the-format).
A DATE- or TIME-declared field formatted as a complete instant is an admitted source, while a
DATE_TIME-declared bare clock is refused on components — so DATE_TIME appears on both sides and no
row reads as one kind being privileged. The conjunct these rows replaced refused both cross-kind
admissions, and this gate is shared with the two shifted-difference carriers, which were measured
separately rather than inherited. -/
example :
    (elaborateTimeFromDateTimeComputation model dateAsStamp.id
      target.id).isOk = true ∧
      (elaborateTimeFromDateTimeComputation model timeAsStamp.id
        target.id).isOk = true ∧
      (match elaborateTimeFromDateTimeComputation model stampAsClock.id
          target.id with
        | .error (.source (.sourceComponents field components)) =>
            field == stampAsClock.id && components == TemporalComponents.time
        | _ => false) = true := by
  native_decide

/- A clean source-identical extracted Time remains a value but produces no changed action. -/
example : resultSummary? [
    sourceCell "2024-06-15T00:30:00" (.parsed (.temporal moment)),
    timeCell target.id extracted.text oldTarget] [.malformed] = some {
      values := [extracted.text]
      changes := []
      cleared := []
      residual := [.malformed]
    } := by
  native_decide

/- Clean absence and formal invalidity remain distinct rich outcomes and both clear an immutable source-filled target. -/
example :
    outcome? [] = some .noValue ∧
    outcome? [sourceCell "bad" (.rejected .dateFormat)] =
      some (.poison .dateFormat) ∧
    resultSummary? [timeCell target.id "07:15:00" differentTarget] = some {
      values := []
      changes := []
      cleared := [target.id]
      residual := []
    } ∧
    resultSummary? [
      sourceCell "bad" (.rejected .dateFormat),
      timeCell target.id "07:15:00" differentTarget] = some {
        values := []
        changes := []
        cleared := [target.id]
        residual := []
      } := by
  native_decide

/- Source-relative application preserves a different destination target when extraction produced no changed action, and also preserves unrelated Time state. -/
example : appliedStates?
    [sourceCell "2024-06-15T00:30:00" (.parsed (.temporal moment)),
      timeCell target.id extracted.text oldTarget]
    [timeCell target.id "07:15:00" differentTarget,
      timeCell other.id "08:45:00" unrelatedTarget] =
    some (.presentValue ⟨"07:15:00", by decide⟩,
      .presentValue ⟨"08:45:00", by decide⟩) := by
  native_decide

end A12Kernel.Conformance.TimeFromDateTimeComputation
