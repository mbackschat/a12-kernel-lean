import A12Kernel.Elaboration.TemporalComputationResult

/-! # DateRange computation result locks -/

namespace A12Kernel.Conformance.DateRangeComputationResult

open A12Kernel

private def target : FlatFieldDecl := {
  id := 1
  groupPath := ["Order"]
  name := "Window"
  policy := { kind := .dateRange }
  dateRangePolicy := some { format := "yyyy-MM-dd", separator := "/" }
}

private def model : FlatModel := {
  fields := [target]
  timeZoneId := "UTC"
}

private def prepared :=
  (prepareFlatStringContext { now := { epochMillis := 0 } }
    builtinStringPatternCompiler model).toOption.get (by native_decide)

private def oldValue : StoredDateRange :=
  ⟨"2024-06-01/2024-06-30", by decide⟩

private def nextValue : StoredDateRange :=
  ⟨"2024-07-01/2024-07-31", by decide⟩

private def source (stored : String) : DocumentData := {
  instantiatedRows := []
  cells := [{
    address := { field := target.id, path := [] }
    stored
    raw := (classifyStoredDateRangeForModel "UTC" none
      { format := "yyyy-MM-dd", separator := "/" } stored).toOption.getD .empty
  }]
}

private def emptySource : DocumentData := { instantiatedRows := [], cells := [] }

private def view? (input : DocumentData) (outcomes : List (FieldId × DateRangeTargetOutcome))
    (messages : List FormalCause := []) :
    Option (DateRangeComputationRunView FormalCause) := do
  let checked ← (checkDocument prepared "en_US" input).toOption
  pure (DateRangeComputationRunView.fromOutcomes checked messages outcomes)

/- An unchanged accepted instance appears only in the complete success channel. -/
example :
    (view? (source oldValue.text) [(target.id, .accepted oldValue)]).map
      (fun view => (view.withoutErrors, view.withChanges,
        view.withErrors, view.cleared)) =
        some ([{ targetField := target.id, value := oldValue }],
          ([] : List DateRangeComputedInstance),
          ([] : List DateRangeComputedError), ([] : List FieldId)) := by
  native_decide

/- A changed accepted instance appears in both success channels and neither failure channel. -/
example :
    (view? (source oldValue.text) [(target.id, .accepted nextValue)]).map
      (fun view => (view.withoutErrors, view.withChanges,
        view.withErrors, view.cleared)) =
        some ([{ targetField := target.id, value := nextValue }],
          [{ targetField := target.id, value := nextValue }],
          ([] : List DateRangeComputedError), ([] : List FieldId)) := by
  native_decide

/- A rejected attempt appears only in the target-error channel. -/
example : (view? (source oldValue.text)
    [(target.id, .errored nextValue .inverted)]).map
      (fun view => (view.withoutErrors, view.withChanges,
        view.withErrors, view.cleared)) =
    some ([], [],
      [{ targetField := target.id, attempted := nextValue, cause := .inverted }],
      []) := by
  native_decide

/- Quiet no-value clears only a source-filled target and never becomes a computed error. -/
example :
    (view? (source oldValue.text) [(target.id, .noValue)]).map
      (fun view => (view.cleared, view.withErrors)) = some ([target.id], []) ∧
    (view? (source "") [(target.id, .noValue)]).map
      (fun view => (view.cleared, view.withErrors)) = some ([], []) ∧
    (view? emptySource [(target.id, .noValue)]).map
      (fun view => (view.cleared, view.withErrors)) = some ([], []) := by
  native_decide

/- Poison follows no-value clearing rather than becoming a target error or minting an absent-source action. -/
example :
    (view? (source oldValue.text) [(target.id, .poison .malformed)]).map
      (fun view => (view.cleared, view.withErrors)) = some ([target.id], []) ∧
    (view? emptySource [(target.id, .poison .malformed)]).map
      (fun view => (view.cleared, view.withErrors)) = some ([], []) := by
  native_decide

/- The public error predicate observes both error channels and accepts a clean unchanged success. -/
example :
    (view? (source oldValue.text) [(target.id, .accepted oldValue)]).map
      (·.noErrorOccurred) = some true ∧
    (view? (source oldValue.text)
      [(target.id, .errored nextValue .inverted)]).map
        (·.noErrorOccurred) = some false ∧
    (view? (source oldValue.text)
      [(target.id, .accepted oldValue)] [.malformed]).map
        (·.noErrorOccurred) = some false := by
  native_decide

/- Residual messages do not change any already-classified result channel. -/
example : (view? (source oldValue.text)
    [(target.id, .accepted nextValue)] [.malformed]).map
      (fun view => (view.withoutErrors, view.withChanges,
        view.withErrors, view.cleared)) =
    some ([{ targetField := target.id, value := nextValue }],
      [{ targetField := target.id, value := nextValue }],
      ([] : List DateRangeComputedError), ([] : List FieldId)) := by
  native_decide

/- The supplied residual message channel remains exact. -/
example : (view? (source oldValue.text)
    [(target.id, .accepted nextValue)] [.malformed]).map
      (fun view => view.formalErrorsInOperands) = some [.malformed] := by
  native_decide

end A12Kernel.Conformance.DateRangeComputationResult
