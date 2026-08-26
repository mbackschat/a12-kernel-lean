import A12Kernel.Elaboration.FullDateComputationApplication

/-! # Full-Date V2 result projection locks -/

namespace A12Kernel.Conformance.FullDateComputationResult

open A12Kernel

private def target : FlatFieldDecl := {
  id := 1
  groupPath := ["Order"]
  name := "Date"
  policy := { kind := .temporal .date TemporalComponents.fullDate }
  temporalTargetPolicy := some {
    format := "dd.MM.yyyy"
    partialMode := .full
  } }

private def other : FlatFieldDecl := {
  target with id := 2, name := "OtherDate"
}

private def stringTarget : FlatFieldDecl := {
  id := 3
  groupPath := ["Order"]
  name := "Label"
  policy := { kind := .string }
}

private def repeatedTarget : FlatFieldDecl := {
  target with
  id := 4
  groupPath := ["Order", "Lines"]
  name := "RepeatedDate"
  repeatableScope := [10]
}

private def incompleteTarget : FlatFieldDecl := {
  target with
  id := 5
  name := "MonthDate"
  policy := { kind := .temporal .date {
    TemporalComponents.fullDate with day := false
  } }
  temporalTargetPolicy := some {
    format := "yyyy-MM"
    partialMode := .dayOptional
  }
}

private def repeatedStringTarget : FlatFieldDecl := {
  stringTarget with
  id := 6
  groupPath := ["Order", "Lines"]
  name := "RepeatedLabel"
  repeatableScope := [10]
}

private def model : FlatModel := {
  fields := [target, other]
}

private def validationModel : FlatModel := {
  fields := [stringTarget, repeatedTarget, incompleteTarget,
    repeatedStringTarget]
  repeatableGroups := [{
    level := 10
    path := ["Order", "Lines"]
    repeatability := some 3
  }]
}

private def prepared :=
  (prepareFlatStringContext { now := { epochMillis := 0 } }
    builtinStringPatternCompiler model).toOption.get (by native_decide)

private def oldDate : StoredDate := ⟨"06.04.2024", by decide⟩
private def nextDate : StoredDate := ⟨"07.04.2024", by decide⟩
private def otherDate : StoredDate := ⟨"08.04.2024", by decide⟩

private def sourceAt (field : FieldId) (stored : String)
    (raw : RawCell) : DocumentData := {
  instantiatedRows := []
  cells := [{ address := { field, path := [] }, stored, raw }]
}

private def source (stored : String) (raw : RawCell) : DocumentData :=
  sourceAt target.id stored raw

private def oldSource : DocumentData :=
  source oldDate.text (.parsed (.temporal (.date {
    instant := { epochMillis := 0 }
    parts := { year := 2024, month := 4, day := 6 }
    basis := .storedGregorian })))

private def view? (input : DocumentData) (outcome : FullDateTargetOutcome)
    (messages : List FormalCause := []) :
    Option (FullDateComputationRunView FormalCause) := do
  let checked ← (checkDocument prepared "en_US" input).toOption
  pure (FullDateComputationRunView.fromOutcomes checked messages
    [(target.id, outcome)])

private def checked? (input : DocumentData) : Option (CheckedDocument model) :=
  (checkDocument prepared "en_US" input).toOption

private def sourceState? (input : DocumentData) : Option FullDateTargetState := do
  let checked ← (checkDocument prepared "en_US" input).toOption
  pure (checked.sourceFullDateTargetState target.id)

private def destinationWith (state : FullDateTargetState) :
    FullDateComputationDestination :=
  fun field => if field == target.id then state else .absent

/- Source recovery retains placement while accepting the stored Date text as an opaque identity. -/
example :
    sourceState? { instantiatedRows := [], cells := [] } = some .absent ∧
      sourceState? (source "" .presentEmpty) = some .presentEmpty ∧
      sourceState? oldSource = some (.presentValue oldDate) := by
  native_decide

/- Successful unchanged instances remain public but are not changes. -/
example : (do
    let view ← view? oldSource (.accepted oldDate)
    pure (view.withoutErrors, view.withChanges)) =
      some ([{ targetField := target.id, value := oldDate }], []) := by
  native_decide

/- A changed value is present in both successful projections. -/
example : (do
    let view ← view? oldSource (.accepted nextDate)
    pure (view.withoutErrors, view.withChanges)) =
      some ([{ targetField := target.id, value := nextDate }],
        [{ targetField := target.id, value := nextDate }]) := by
  native_decide

/- Rejection is a computed-instance error, never a clear. -/
example : (do
    let view ← view? oldSource (.errored nextDate .before1900)
    pure (view.withErrors, view.cleared)) =
      some ([{ targetField := target.id, attempted := nextDate, cause := .before1900 }], []) := by
  native_decide

/- Quiet no-value and poison clear only a source-filled target. -/
example :
    (view? oldSource .noValue).map (·.cleared) = some [target.id] ∧
    (view? { instantiatedRows := [], cells := [] } .noValue).map (·.cleared) =
      some [] ∧
    (view? oldSource (.poison .malformed)).map
      (fun view => (view.cleared, view.noErrorOccurred)) =
        some ([target.id], true) := by
  native_decide

/- Residual messages alone make the exact two-channel predicate false. -/
example :
    (view? { instantiatedRows := [], cells := [] } .noValue
      [.malformed]).map (fun view =>
        (view.formalErrorsInOperands, view.noErrorOccurred)) =
      some ([.malformed], false) := by
  native_decide

/- Source-unchanged success is not reclassified against a different destination. -/
example : (do
    let view ← view? oldSource (.accepted oldDate)
    let applied ← view.applyTo (destinationWith (.presentValue nextDate)) |>.toOption
    pure (applied target.id)) = some (.presentValue nextDate) := by
  native_decide

/- Changed success writes, rejection retains its guarded direct transition, and public clearing creates a present-empty target when the destination target was absent. -/
example :
    (do
      let view ← view? oldSource (.accepted nextDate)
      let applied ← view.applyTo (destinationWith .absent) |>.toOption
      pure (applied target.id)) = some (.presentValue nextDate) ∧
    (do
      let view ← view? oldSource (.errored nextDate .before1900)
      let applied ← view.applyTo (destinationWith (.presentValue nextDate)) |>.toOption
      pure (applied target.id)) = some .presentEmpty ∧
    (do
      let view ← view? oldSource .noValue
      let applied ← view.applyTo (destinationWith (.presentValue nextDate)) |>.toOption
      pure (applied target.id)) = some .presentEmpty ∧
    (do
      let view ← view? oldSource .noValue
      let applied ← view.applyTo (destinationWith .absent) |>.toOption
      pure (applied target.id)) = some .presentEmpty := by
  native_decide

/- A malformed result cannot let action-list order choose between writes at one target. -/
example : (do
    let checked ← (checkDocument prepared "en_US" oldSource).toOption
    let view := FullDateComputationRunView.fromOutcomes checked
      ([] : List FormalCause)
      [(target.id, .accepted nextDate),
        (target.id, .errored nextDate .before1900)]
    pure (match view.applyTo (destinationWith .absent) with
      | .error error => some error
      | .ok _ => none)) =
        some (some (.duplicateActionTarget target.id)) := by
  native_decide

/- Checked application starts from the separately supplied document's exact FullDate placement and preserves an unrelated Date field. -/
example : (do
    let view ← view? oldSource (.accepted nextDate)
    let checked ← checked? {
      instantiatedRows := []
      cells := oldSource.cells ++ (sourceAt other.id otherDate.text
        (.parsed (.temporal (.date {
          instant := { epochMillis := 172800000 }
          parts := { year := 2024, month := 4, day := 8 }
          basis := .storedGregorian })))).cells
    }
    let applied ← view.applyToChecked checked |>.toOption
    pure (applied target.id, applied other.id)) =
      some (.presentValue nextDate, .presentValue otherDate) := by
  native_decide

/- Checked target validation retains the exact unknown cause and separates wrong-family from repeatable FullDate targets. -/
example :
    (match FullDateComputationRunView.validateActionTargets
        validationModel [99] with
      | .error (.targetField 99 (.unknownFieldId 99)) => true
      | _ => false) = true ∧
    (match FullDateComputationRunView.validateActionTargets
        validationModel [stringTarget.id] with
      | .error (.nonFullDateTarget field) => field == stringTarget.id
      | _ => false) = true ∧
    (match FullDateComputationRunView.validateActionTargets
        validationModel [repeatedTarget.id] with
      | .error (.repeatableTarget field) => field == repeatedTarget.id
      | _ => false) = true := by
  native_decide

/- Incomplete Date components remain outside the FullDate result family. -/
example : (match FullDateComputationRunView.validateActionTargets
    validationModel [incompleteTarget.id] with
  | .error (.nonFullDateTarget field) => field == incompleteTarget.id
  | _ => false) = true := by
  native_decide

/- A repeatable wrong-kind target reports its family mismatch before its scope mismatch. -/
example : (match FullDateComputationRunView.validateActionTargets
    validationModel [repeatedStringTarget.id] with
  | .error (.nonFullDateTarget field) => field == repeatedStringTarget.id
  | _ => false) = true := by
  native_decide

/- Duplicate actions fail before checked target validation. -/
example : (do
    let checked ← checked? { instantiatedRows := [], cells := [] }
    let empty ← checked? { instantiatedRows := [], cells := [] }
    let view := FullDateComputationRunView.fromOutcomes empty
      ([] : List FormalCause)
      [(99, .accepted nextDate), (99, .errored oldDate .before1900)]
    pure (match view.applyToChecked checked with
      | .error (.duplicateActionTarget field) => field == 99
      | _ => false)) = some true := by
  native_decide

end A12Kernel.Conformance.FullDateComputationResult
