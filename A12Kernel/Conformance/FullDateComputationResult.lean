import A12Kernel.Elaboration.FullDateComputationResult

/-! # Full-Date V2 result projection locks -/

namespace A12Kernel.Conformance.FullDateComputationResult

open A12Kernel

private def target : FlatFieldDecl := {
  id := 1
  groupPath := ["Order"]
  name := "Date"
  policy := { kind := .temporal .date TemporalComponents.fullDate } }

private def model : FlatModel := { fields := [target] }

private def prepared :=
  (prepareFlatStringContext { now := { epochMillis := 0 } }
    builtinStringPatternCompiler model).toOption.get (by native_decide)

private def oldDate : StoredDate := ⟨"06.04.2024", by decide⟩
private def nextDate : StoredDate := ⟨"07.04.2024", by decide⟩

private def source (stored : String) (raw : RawCell) : DocumentData := {
  instantiatedRows := []
  cells := [{ address := { field := target.id, path := [] }, stored, raw }] }

private def oldSource : DocumentData :=
  source oldDate.text (.parsed (.temporal (.date { epochMillis := 0 }
    { year := 2024, month := 4, day := 6 } .storedGregorian)))

private def view? (input : DocumentData) (outcome : FullDateTargetOutcome)
    (messages : List FormalCause := []) :
    Option (FullDateComputationRunView FormalCause) := do
  let checked ← (checkDocument prepared "en_US" input).toOption
  pure (FullDateComputationRunView.fromOutcomes checked messages
    [(target.id, outcome)])

private def sourceState? (input : DocumentData) : Option FullDateTargetState := do
  let checked ← (checkDocument prepared "en_US" input).toOption
  pure (checked.sourceFullDateTargetState target.id)

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

end A12Kernel.Conformance.FullDateComputationResult
