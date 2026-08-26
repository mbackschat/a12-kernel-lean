import A12Kernel.Elaboration.TemporalComputationResult

/-! # DateRange source target-state locks -/

namespace A12Kernel.Conformance.DateRangeSourceTargetState

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

private def source (stored : String) : DocumentData := {
  instantiatedRows := []
  cells := [{
    address := { field := target.id, path := [] }
    stored
    raw := (classifyStoredDateRangeForModel "UTC" none
      { format := "yyyy-MM-dd", separator := "/" } stored).toOption.getD .empty
  }]
}

private def state? (input : DocumentData) :
    Option (TemporalTargetState StoredDateRange) := do
  let checked ← (checkDocument prepared "en_US" input).toOption
  pure (checked.sourceDateRangeTargetState target.id)

/- Exact placement distinguishes absent, present-empty, and a canonical nonempty spelling. -/
example :
    state? { instantiatedRows := [], cells := [] } = some .absent ∧
    state? (source "") = some .presentEmpty ∧
    state? (source "2024-06-01/2024-06-30") =
      some (.presentValue ⟨"2024-06-01/2024-06-30", by decide⟩) := by
  native_decide

/- A formally rejected nonempty source retains its exact stored text instead of being parsed away or re-rendered. -/
example : state? (source "x") = some (.presentValue ⟨"x", by decide⟩) := by
  native_decide

end A12Kernel.Conformance.DateRangeSourceTargetState
