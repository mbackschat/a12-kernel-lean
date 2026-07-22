import A12Kernel.Elaboration.StarGroup

/-! # Laws for checked terminal-repeatable group-star consumers -/

namespace A12Kernel

/-- Checked group lowering retains the model-derived outer-to-inner repeatable ancestry. -/
@[simp] theorem checkedStarredGroupSource_ancestry
    (checked : CheckedStarredGroupSource model) :
    checked.path.axes.map (·.level) =
      model.repeatableScopeForGroupPath checked.group.path :=
  checked.ancestryOwned

/-- No instantiated terminal row is exactly the omission-typed firing region. -/
@[simp] theorem starredGroup_noGroupFilled_zero :
    StarredGroupFillQuantifier.noGroupFilled.evalCount 0 =
      .fired .omission := by
  rfl

/-- Any instantiated terminal row prevents `NoGroupFilled(G*)`. -/
@[simp] theorem starredGroup_noGroupFilled_successor (count : Nat) :
    StarredGroupFillQuantifier.noGroupFilled.evalCount (count + 1) =
      .falseOrUnknown := by
  simp [StarredGroupFillQuantifier.evalCount,
    StarredGroupFillQuantifier.toGroupFillQuantifier,
    GroupFillQuantifier.evalTally]

/-- No instantiated terminal row cannot satisfy `AtLeastOneGroupFilled(G*)`. -/
@[simp] theorem starredGroup_atLeastOne_zero :
    StarredGroupFillQuantifier.atLeastOneGroupFilled.evalCount 0 =
      .falseOrUnknown := by
  rfl

/-- One or more instantiated terminal rows give the value-typed positive witness. -/
@[simp] theorem starredGroup_atLeastOne_successor (count : Nat) :
    StarredGroupFillQuantifier.atLeastOneGroupFilled.evalCount (count + 1) =
      .fired .value := by
  simp [StarredGroupFillQuantifier.evalCount,
    StarredGroupFillQuantifier.toGroupFillQuantifier,
    GroupFillQuantifier.evalTally]

/-- Runtime counting is exactly the cardinality of the canonical terminal-row environment stream. -/
theorem checkedStarredGroupSource_rowCount_of_resolved
    (checked : CheckedStarredGroupSource model) (document : Document)
    (outer : Env) (resolved : ResolvedStarTopology)
    (resolution : checked.resolvedTopology document outer = .ok resolved) :
    checked.rowCount document outer = .ok resolved.environments.length := by
  unfold CheckedStarredGroupSource.rowCount
  rw [resolution]
  rfl

/-- Both legal predicates consume the same successful topology cardinality without a second row walk. -/
theorem checkedStarredGroupSource_evaluateFull_of_resolved
    (checked : CheckedStarredGroupSource model)
    (operator : StarredGroupFillQuantifier) (document : Document)
    (outer : Env) (resolved : ResolvedStarTopology)
    (resolution : checked.resolvedTopology document outer = .ok resolved) :
    checked.evaluateFull operator document outer =
      .ok (operator.evalCount resolved.environments.length) := by
  unfold CheckedStarredGroupSource.evaluateFull
    CheckedStarredGroupSource.rowCount
  rw [resolution]
  rfl

/-- The starred numeric count consumes that identical successful topology cardinality. -/
theorem checkedStarredGroupSource_numberOfFilledGroups_of_resolved
    (checked : CheckedStarredGroupSource model) (document : Document)
    (outer : Env) (resolved : ResolvedStarTopology)
    (resolution : checked.resolvedTopology document outer = .ok resolved) :
    checked.numberOfFilledGroups document outer =
      .ok (.value resolved.environments.length) := by
  unfold CheckedStarredGroupSource.numberOfFilledGroups
    CheckedStarredGroupSource.rowCount
  rw [resolution]
  rfl

end A12Kernel
