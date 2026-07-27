import A12Kernel.Elaboration.TemporalComputationResult

/-! # DateTime V2 result projection locks -/

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

end A12Kernel.Conformance.DateTimeComputationResult
