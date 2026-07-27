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

private def model : FlatModel := { fields := [target] }

private def prepared :=
  (prepareFlatStringContext { now := { epochMillis := 0 } }
    builtinStringPatternCompiler model).toOption.get (by native_decide)

private def oldValue : StoredDateTime :=
  ⟨"23.06.2025T09:59:59", by decide⟩

private def nextValue : StoredDateTime :=
  ⟨"23.06.2025T10:00:00", by decide⟩

private def source (stored : String) (raw : RawCell) : DocumentData := {
  instantiatedRows := []
  cells := [{
    address := { field := target.id, path := [] }
    stored
    raw }] }

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

/- Changed success writes, while public clearing uses the existing one-target transition. -/
example :
    (do
      let view ← view? oldSource (.accepted nextValue)
      let applied ← view.applyTo (destinationWith .absent) |>.toOption
      pure (applied target.id)) = some (.presentValue nextValue) ∧
    (do
      let view ← view? oldSource .noValue
      let applied ← view.applyTo
        (destinationWith (.presentValue nextValue)) |>.toOption
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

end A12Kernel.Conformance.DateTimeComputationResult
