import A12Kernel.Elaboration.TemporalErroredComputationApplication

/-! # DateRange whole-result application locks -/

namespace A12Kernel.Conformance.DateRangeComputationApplication

open A12Kernel

private def rangeField (id : FieldId) (name : String) : FlatFieldDecl := {
  id
  groupPath := ["Order"]
  name
  policy := { kind := .dateRange }
  dateRangePolicy := some { format := "yyyy-MM-dd", separator := "/" }
}

private def target := rangeField 1 "Window"
private def other := rangeField 2 "Other"
private def errorTarget := rangeField 3 "Rejected"
private def changeTarget := rangeField 4 "Changed"

private def model : FlatModel := {
  fields := [target, other, errorTarget, changeTarget]
  timeZoneId := "UTC"
}

private def prepared :=
  (prepareFlatStringContext { now := { epochMillis := 0 } }
    builtinStringPatternCompiler model).toOption.get (by native_decide)

private def oldValue : StoredDateRange :=
  ⟨"2024-06-01/2024-06-30", by decide⟩

private def nextValue : StoredDateRange :=
  ⟨"2024-07-01/2024-07-31", by decide⟩

private def source (values : List (FieldId × StoredDateRange)) : DocumentData := {
  instantiatedRows := []
  cells := values.map fun (field, value) => {
    address := { field, path := [] }
    stored := value.text
    raw := (classifyStoredDateRangeForModel "UTC" none
      { format := "yyyy-MM-dd", separator := "/" }
      value.text).toOption.getD .empty
  }
}

private def view? (input : DocumentData)
    (outcomes : List (FieldId × DateRangeTargetOutcome))
    (messages : List FormalCause := []) :
    Option (DateRangeComputationRunView FormalCause) := do
  let checked ← (checkDocument prepared "en_US" input).toOption
  pure (DateRangeComputationRunView.fromOutcomes checked messages outcomes)

private def destination
    (targetState otherState : TemporalTargetState StoredDateRange) :
    DateRangeComputationDestination :=
  fun field =>
    if field == target.id then targetState
    else if field == other.id then otherState
    else .absent

/- An unchanged success is not reclassified against the destination; a changed success writes exactly once. -/
example :
    (do
      let view ← view? (source [(target.id, oldValue)])
        [(target.id, .accepted oldValue)]
      let applied ← view.applyTo
        (destination (.presentValue nextValue) (.presentValue oldValue)) |>.toOption
      pure (applied target.id, applied other.id)) =
        some (.presentValue nextValue, .presentValue oldValue) ∧
    (do
      let view ← view? (source [(target.id, oldValue)])
        [(target.id, .accepted nextValue)]
      let applied ← view.applyTo (destination .absent (.presentValue oldValue)) |>.toOption
      pure (applied target.id, applied other.id)) =
        some (.presentValue nextValue, .presentValue oldValue) := by
  native_decide

/- A rejected attempt clears an existing destination target but never creates an absent one. -/
example :
    (do
      let view ← view? (source [])
        [(target.id, .errored nextValue .inverted)]
      let applied ← view.applyTo (destination (.presentValue oldValue) .absent) |>.toOption
      pure (applied target.id)) = some .presentEmpty ∧
    (do
      let view ← view? (source [])
        [(target.id, .errored nextValue .inverted)]
      let applied ← view.applyTo (destination .absent .absent) |>.toOption
      pure (applied target.id)) = some .absent := by
  native_decide

/- A retained clear creates present-empty placement and preserves an unrelated destination value exactly. -/
example : (do
    let view ← view? (source [(target.id, oldValue)])
      [(target.id, .noValue)]
    let applied ← view.applyTo
      (destination .absent (.presentValue oldValue)) |>.toOption
    pure (applied target.id, applied other.id)) =
      some (.presentEmpty, .presentValue oldValue) := by
  native_decide

/- Source absence mints no action even when the destination target is filled. -/
example : (do
    let view ← view? (source []) [(target.id, .noValue)]
    let applied ← view.applyTo
      (destination (.presentValue oldValue) .absent) |>.toOption
    pure (applied target.id)) = some (.presentValue oldValue) := by
  native_decide

private def mixedView? := view? (source [(target.id, oldValue),
    (changeTarget.id, oldValue)])
    [(changeTarget.id, .accepted nextValue),
      (errorTarget.id, .errored nextValue .inverted),
      (target.id, .noValue)]

/- Application selects clears, errors, then changes, independent of authored outcome order. -/
example : mixedView?.map DateRangeComputationRunView.actionTargets =
    some [target.id, errorTarget.id, changeTarget.id] := by
  native_decide

/- The shared fold consumes the selected categories in that same order. -/
example : mixedView?.map (fun view =>
    match (TemporalErroredComputationRunView.applyTo view
      ([] : List FieldId)
      (fun computed => computed.targetField)
      (fun computed => computed.targetField) (fun field : FieldId => field)
      (fun current field => current ++ [field])
      (fun current computed => current ++ [computed.targetField])
      (fun current computed => current ++ [computed.targetField]) :
        Except FieldId (List FieldId)) with
    | .ok trace => some trace
    | .error _ => none) =
    some (some [target.id, errorTarget.id, changeTarget.id]) := by
  native_decide

/- Residual messages never alter application actions. -/
example : (do
    let clean ← view? (source [(target.id, oldValue)])
      [(target.id, .accepted nextValue)]
    let residual ← view? (source [(target.id, oldValue)])
      [(target.id, .accepted nextValue)] [.malformed]
    let cleanApplied ← clean.applyTo (destination .absent .absent) |>.toOption
    let residualApplied ← residual.applyTo (destination .absent .absent) |>.toOption
    pure (cleanApplied target.id, residualApplied target.id)) =
      some (.presentValue nextValue, .presentValue nextValue) := by
  native_decide

/- Duplicate action targets fail before the destination participates. -/
example : (do
    let view ← view? (source [(target.id, oldValue)])
      [(target.id, .accepted nextValue), (target.id, .noValue)]
    pure (match view.applyTo (destination .absent .absent) with
      | .error error => some error
      | .ok _ => none)) =
      some (some (.duplicateActionTarget target.id)) := by
  native_decide

end A12Kernel.Conformance.DateRangeComputationApplication
