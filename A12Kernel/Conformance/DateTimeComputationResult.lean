import A12Kernel.Elaboration.DateTimeComputationApplication

/-! # DateTime V2 result and application locks -/

namespace A12Kernel.Conformance.DateTimeComputationResult

open A12Kernel

private def target : FlatFieldDecl := {
  id := 1
  groupPath := ["Order"]
  name := "CalculatedAt"
  policy := {
    kind := .temporal .dateTime TemporalComponents.now } }

private def other : FlatFieldDecl := {
  target with id := 2, name := "OtherAt"
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
  name := "RepeatedAt"
  repeatableScope := [10]
}

private def incompleteTarget : FlatFieldDecl := {
  target with
  id := 5
  name := "MinuteAt"
  policy := { kind := .temporal .dateTime {
    TemporalComponents.now with second := false
  } }
}

private def repeatedStringTarget : FlatFieldDecl := {
  stringTarget with
  id := 6
  groupPath := ["Order", "Lines"]
  name := "RepeatedLabel"
  repeatableScope := [10]
}

private def model : FlatModel := { fields := [target, other] }

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

private def oldValue : StoredDateTime :=
  ⟨"23.06.2025T09:59:59", by decide⟩

private def nextValue : StoredDateTime :=
  ⟨"23.06.2025T10:00:00", by decide⟩

private def otherValue : StoredDateTime :=
  ⟨"23.06.2025T11:00:00", by decide⟩

private def sourceAt (field : FieldId) (stored : String)
    (raw : RawCell) : DocumentData := {
  instantiatedRows := []
  cells := [{
    address := { field, path := [] }
    stored
    raw }] }

private def source (stored : String) (raw : RawCell) : DocumentData :=
  sourceAt target.id stored raw

private def oldSource : DocumentData :=
  source oldValue.text (.parsed (.temporal
    (.dateTime { epochMillis := 0 }
      { year := 2025, month := 6, day := 23 }
      { hour := 9, minute := 59, second := 59, valid := by decide }
      .storedGregorian)))

private def view? (input : DocumentData)
    (outcome : DateTimeTargetOutcome)
    (messages : List FormalCause := []) :
    Option (DateTimeComputationRunView FormalCause) := do
  let checked ← (checkDocument prepared "en_US" input).toOption
  pure (DateTimeComputationRunView.fromOutcomes checked messages
    [(target.id, outcome)])

private def checked? (input : DocumentData) : Option (CheckedDocument model) :=
  (checkDocument prepared "en_US" input).toOption

private def sourceState? (input : DocumentData) :
    Option DateTimeTargetState := do
  let checked ← (checkDocument prepared "en_US" input).toOption
  pure (checked.sourceDateTimeTargetState target.id)

private def destinationWith (state : DateTimeTargetState) :
    DateTimeComputationDestination :=
  fun field => if field == target.id then state else .absent

/- Source recovery retains absent, present-empty, and exact stored DateTime text without reparsing. -/
example :
    sourceState? { instantiatedRows := [], cells := [] } = some .absent ∧
      sourceState? (source "" .presentEmpty) = some .presentEmpty ∧
      sourceState? oldSource = some (.presentValue oldValue) := by
  native_decide

/- Accepted unchanged text remains public but is not a change; a changed value appears in both successful projections. -/
example :
    (view? oldSource (.accepted oldValue)).map
        (fun view => (view.withoutErrors, view.withChanges)) =
      some ([{ targetField := target.id, value := oldValue }], []) ∧
    (view? oldSource (.accepted nextValue)).map
        (fun view => (view.withoutErrors, view.withChanges)) =
      some ([{ targetField := target.id, value := nextValue }],
        [{ targetField := target.id, value := nextValue }]) := by
  native_decide

/- Quiet no-value and poison clear only a source-filled target and manufacture no computed-instance error. -/
example :
    (view? oldSource .noValue).map
        (fun view => (view.cleared, view.withErrors)) =
      some ([target.id], []) ∧
    (view? { instantiatedRows := [], cells := [] } .noValue).map
        (·.cleared) = some [] ∧
    (view? oldSource (.poison .malformed)).map
        (fun view => (view.cleared, view.noErrorOccurred)) =
      some ([target.id], true) := by
  native_decide

/- Residual messages are the only reachable DateTime error channel in this bounded target fragment. -/
example :
    (view? { instantiatedRows := [], cells := [] } .noValue
      [.malformed]).map (fun view =>
        (view.withErrors, view.formalErrorsInOperands,
          view.noErrorOccurred)) =
      some ([], [.malformed], false) := by
  native_decide

/- Source-unchanged success remains public but is not reclassified against a different destination. -/
example : (do
    let view ← view? oldSource (.accepted oldValue)
    let applied ← view.applyTo
      (destinationWith (.presentValue nextValue)) |>.toOption
    pure (applied target.id)) = some (.presentValue nextValue) := by
  native_decide

/- Changed success writes, while a source-classified public clear creates a present-empty target when the destination target was absent. -/
example :
    (do
      let view ← view? oldSource (.accepted nextValue)
      let applied ← view.applyTo (destinationWith .absent) |>.toOption
      pure (applied target.id)) = some (.presentValue nextValue) ∧
    (do
      let view ← view? oldSource .noValue
      let applied ← view.applyTo
        (destinationWith (.presentValue nextValue)) |>.toOption
      pure (applied target.id)) = some .presentEmpty ∧
    (do
      let view ← view? oldSource .noValue
      let applied ← view.applyTo (destinationWith .absent) |>.toOption
      pure (applied target.id)) = some .presentEmpty := by
  native_decide

/- Residual messages change error status but never the already-classified actions. -/
example : (do
    let view ← view? oldSource (.accepted nextValue) [.malformed]
    let applied ← view.applyTo (destinationWith .absent) |>.toOption
    pure (applied target.id, view.noErrorOccurred)) =
      some (.presentValue nextValue, false) := by
  native_decide

/- A malformed result cannot let action order choose between clear and write at one target. -/
example : (do
    let checked ← (checkDocument prepared "en_US" oldSource).toOption
    let view := DateTimeComputationRunView.fromOutcomes checked
      ([] : List FormalCause)
      [(target.id, .accepted nextValue), (target.id, .noValue)]
    pure (match view.applyTo (destinationWith .absent) with
      | .error error => some error
      | .ok _ => none)) =
        some (some (.duplicateActionTarget target.id)) := by
  native_decide

/- Checked application starts from the separately supplied document's exact DateTime placement and preserves a distinct unrelated value. -/
example : (do
    let view ← view? oldSource (.accepted nextValue)
    let checked ← checked? {
      instantiatedRows := []
      cells := oldSource.cells ++ (sourceAt other.id otherValue.text
        (.parsed (.temporal
          (.dateTime { epochMillis := 7200000 }
            { year := 2025, month := 6, day := 23 }
            { hour := 11, minute := 0, second := 0, valid := by decide }
            .storedGregorian)))).cells
    }
    let applied ← view.applyToChecked checked |>.toOption
    pure (applied target.id, applied other.id)) =
      some (.presentValue nextValue, .presentValue otherValue) := by
  native_decide

/- Checked target validation retains the exact lookup cause and separates family and scope failures. -/
example :
    (match DateTimeComputationRunView.validateActionTargets
        validationModel [99] with
      | .error (.targetField 99 (.unknownFieldId 99)) => true
      | _ => false) = true ∧
    (match DateTimeComputationRunView.validateActionTargets
        validationModel [stringTarget.id] with
      | .error (.nonDateTimeTarget field) => field == stringTarget.id
      | _ => false) = true ∧
    (match DateTimeComputationRunView.validateActionTargets
        validationModel [repeatedTarget.id] with
      | .error (.repeatableTarget field) => field == repeatedTarget.id
      | _ => false) = true := by
  native_decide

/- DateTime requires the complete whole-second component set. -/
example : (match DateTimeComputationRunView.validateActionTargets
    validationModel [incompleteTarget.id] with
  | .error (.nonDateTimeTarget field) => field == incompleteTarget.id
  | _ => false) = true := by
  native_decide

/- Family rejection precedes repeatable-scope rejection. -/
example : (match DateTimeComputationRunView.validateActionTargets
    validationModel [repeatedStringTarget.id] with
  | .error (.nonDateTimeTarget field) => field == repeatedStringTarget.id
  | _ => false) = true := by
  native_decide

/- Duplicate actions fail before checked target validation. -/
example : (do
    let checked ← checked? { instantiatedRows := [], cells := [] }
    let empty ← checked? { instantiatedRows := [], cells := [] }
    let view := DateTimeComputationRunView.fromOutcomes empty
      ([] : List FormalCause)
      [(99, .accepted nextValue), (99, .accepted oldValue)]
    pure (match view.applyToChecked checked with
      | .error (.duplicateActionTarget field) => field == 99
      | _ => false)) = some true := by
  native_decide

end A12Kernel.Conformance.DateTimeComputationResult
