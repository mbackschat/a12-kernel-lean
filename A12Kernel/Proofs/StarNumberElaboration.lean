import A12Kernel.Elaboration.StarNumber

namespace A12Kernel

/-- The concrete Number consumer retains the general checked path's exact model ancestry. -/
@[simp] theorem checkedStarNumberSource_ancestry (checked : CheckedStarNumberSource model) :
    checked.source.path.axes.map (·.level) =
      checked.source.declaration.repeatableScope :=
  checked.source.ancestryOwned

/-- Structural over-repetition replaces ordinary scalar findings at the checked cell boundary. -/
theorem checkedStarNumberSource_overLimit (checked : CheckedStarNumberSource model)
    (read : Env → FieldId → RawCell) (environment : Env)
    (overLimit : checked.environmentOverLimit environment = true) :
    (checked.checkedCell read environment).parsed = none ∧
      (checked.checkedCell read environment).findings = [.overRepetition] := by
  simp [CheckedStarNumberSource.checkedCell, overLimit]

/-- A resolved `Having` is retained explicitly for downstream polarity even when it selects no candidate. -/
@[simp] theorem checkedStarNumberSource_havingFlag
    (checked : CheckedStarNumberSource model) (resolved : ResolvedStarTopology)
    (having : CorrelatedHaving) (filterRead : Env → FieldId → CheckedCell)
    (outer : Env) (read : Env → FieldId → RawCell) :
    (checked.selectedValidationHavingValueSide resolved having filterRead outer read).hasHaving =
      true := by
  rfl

/-- Target classification is local to environments already selected by `Having`; changing a dropped target cannot change the resolved side. -/
theorem checkedStarNumberSource_filterBeforeTarget
    (checked : CheckedStarNumberSource model) (resolved : ResolvedStarTopology)
    (having : CorrelatedHaving) (filterRead : Env → FieldId → CheckedCell)
    (outer : Env) (left right : Env → FieldId → RawCell)
    (agree : ∀ environment,
      environment ∈ having.selectEnvironments { read := filterRead } outer
        resolved.environments →
      checked.valueListCell left environment =
        checked.valueListCell right environment) :
    checked.selectedValidationHavingValueSide resolved having filterRead outer left =
      checked.selectedValidationHavingValueSide resolved having filterRead outer right := by
  simp only [CheckedStarNumberSource.selectedValidationHavingValueSide]
  congr 1
  apply List.map_congr_left
  intro environment selected
  exact agree environment selected

end A12Kernel
