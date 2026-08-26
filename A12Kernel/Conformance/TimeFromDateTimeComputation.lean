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

private def model : FlatModel := {
  fields := [source, target, other]
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

/- A clean source-identical Time remains in the changed channel under the measured Time result rule. -/
example : resultSummary? [
    sourceCell "2024-06-15T00:30:00" (.parsed (.temporal moment)),
    timeCell target.id extracted.text oldTarget] [.malformed] = some {
      values := [extracted.text]
      changes := [extracted.text]
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

/- Exact checked application starts from the separate destination and preserves unrelated Time state. -/
example : appliedStates?
    [sourceCell "2024-06-15T00:30:00" (.parsed (.temporal moment))]
    [timeCell target.id "07:15:00" differentTarget,
      timeCell other.id "08:45:00" unrelatedTarget] =
    some (.presentValue extracted,
      .presentValue ⟨"08:45:00", by decide⟩) := by
  native_decide

end A12Kernel.Conformance.TimeFromDateTimeComputation
