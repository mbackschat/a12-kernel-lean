import A12Kernel.Elaboration.StarGroup

/-! # Laws for checked group-star terminal consumers -/

namespace A12Kernel

/-- Checked group lowering retains the model-derived outer-to-inner repeatable ancestry. -/
@[simp] theorem checkedStarredGroupSource_ancestry
    (checked : CheckedStarredGroupSource model) :
    checked.path.axes.map (·.level) =
      model.repeatableScopeForGroupPath checked.group.path :=
  checked.ancestryOwned

/-- Every resolved starred group source discharges the generic checked-core boundary from the certificates produced by its sole elaborator. -/
@[simp] theorem checkedStarredGroupSource_wellFormed
    (checked : CheckedStarredGroupSource model) :
    checked.wellFormedBool checked.declaringGroup = true := by
  have owned : checked.group ∈ model.repeatableGroups := by
    simpa using checked.groupOwned
  simp [CheckedStarredGroupSource.wellFormedBool,
    checked.modelWellFormed, owned, checked.ancestryOwned,
    checked.firstStarWithin, checked.pathValid]

/-- A starred group source cannot be transplanted into a checked condition owned by another declaring group. -/
theorem checkedStarredGroupSource_wellFormed_declaringGroup
    (checked : CheckedStarredGroupSource model) (rowGroup : GroupPath)
    (valid : checked.wellFormedBool rowGroup = true) :
    checked.declaringGroup = rowGroup := by
  simp [CheckedStarredGroupSource.wellFormedBool] at valid
  exact valid.1.1.1.1

/-- Checked nonrepeatable-terminal lowering retains the model-derived outer-to-inner repeatable ancestry. -/
@[simp] theorem checkedStarredGroupPresenceSource_ancestry
    (checked : CheckedStarredGroupPresenceSource model) :
    checked.path.axes.map (·.level) =
      model.repeatableScopeForGroupPath checked.groupPath :=
  checked.ancestryOwned

/-- Every resolved nonrepeatable terminal discharges the generic checked-core boundary from its exact model and topology certificates. -/
@[simp] theorem checkedStarredGroupPresenceSource_wellFormed
    (checked : CheckedStarredGroupPresenceSource model) :
    checked.wellFormedBool checked.declaringGroup = true := by
  simp [CheckedStarredGroupPresenceSource.wellFormedBool,
    checked.modelWellFormed, checked.groupOwned,
    checked.terminalNonrepeatable, checked.ancestryOwned,
    checked.firstStarWithin, checked.pathValid]

/-- A nonrepeatable-terminal starred source cannot be transplanted into a checked condition owned by another declaring group. -/
theorem checkedStarredGroupPresenceSource_wellFormed_declaringGroup
    (checked : CheckedStarredGroupPresenceSource model)
    (rowGroup : GroupPath)
    (valid : checked.wellFormedBool rowGroup = true) :
    checked.declaringGroup = rowGroup := by
  simp [CheckedStarredGroupPresenceSource.wellFormedBool] at valid
  exact valid.1.1.1.1.1

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
    GroupFillQuantifier.evalTally,
    GroupListPresenceTally.filledOnly]

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
    GroupFillQuantifier.evalTally,
    GroupListPresenceTally.filledOnly]

/-- A unique repeatable-path lookup returns a declaration the model actually owns, at exactly
    the requested path. Both facts are re-checked by the group elaborator's defensive branch. -/
private theorem lookupUniqueRepeatablePath_owned (model : FlatModel) (path : GroupPath)
    (group : RepeatableGroupDecl)
    (found : model.lookupUniqueRepeatablePath path = .ok group) :
    group ∈ model.repeatableGroups ∧ group.path = path := by
  unfold FlatModel.lookupUniqueRepeatablePath at found
  cases hFilter : model.repeatableGroups.filter (fun candidate => candidate.path == path) with
  | nil => simp only [hFilter] at found; simp at found
  | cons head tail =>
      cases tail with
      | cons second rest => simp only [hFilter] at found; simp at found
      | nil =>
          simp only [hFilter, Except.ok.injEq] at found
          subst found
          have member : head ∈ model.repeatableGroups.filter
              (fun candidate => candidate.path == path) := by
            rw [hFilter]; simp
          obtain ⟨owned, samePath⟩ := List.mem_filter.mp member
          exact ⟨owned, by simpa using samePath⟩

/-- Checked group lowering never reaches its own defensive incoherent-core branch: the unique
    repeatable lookup already establishes model ownership, and the shared planner already
    establishes the model-derived ancestry the constructor re-checks. -/
theorem elaborateStarredGroupSource_never_incoherentCore
    (model : FlatModel) (declaringGroup : GroupPath) (source : SurfaceStarGroupPath) :
    elaborateStarredGroupSource model declaringGroup source ≠
      .error .incoherentCore := by
  unfold elaborateStarredGroupSource
  split
  · simp
  · split
    · rename_i baseError _
      cases baseError <;> simp [StarredGroupBaseError.toElabError]
    · rename_i basePath _
      split
      · simp
      · rename_i group hLookup
        split
        · simp
        · rename_i plan hPlan
          obtain ⟨member, pathEq⟩ :=
            lookupUniqueRepeatablePath_owned model
              (basePath ++ source.groups.map (·.name)) group hLookup
          have ancestry :=
            elaborateStarPathPlan_ancestry model basePath source.groups
              group.path plan hPlan
          simp [member, pathEq, ancestry]

/-- The shared star planner's defensive incoherent-core branch is likewise dead, so a group
    operand cannot surface it through the mapped `path` channel either. -/
theorem elaborateStarredGroupSource_never_path_incoherentCore
    (model : FlatModel) (declaringGroup : GroupPath) (source : SurfaceStarGroupPath) :
    elaborateStarredGroupSource model declaringGroup source ≠
      .error (.path .incoherentCore) := by
  unfold elaborateStarredGroupSource
  split
  · simp
  · split
    · rename_i baseError _
      cases baseError <;> simp [StarredGroupBaseError.toElabError]
    · rename_i basePath _
      split
      · simp
      · rename_i group _
        split
        · rename_i error hPlan
          have dead := elaborateStarPathPlan_never_incoherentCore model basePath
            source.groups group.path
          rw [hPlan] at dead
          simp only [ne_eq, Except.error.injEq] at dead
          simp [dead]
        · split
          · split <;> simp
          · simp

/-- General starred-group lowering cannot expose its own defensive incoherent-core branch for either terminal interpretation. -/
theorem elaborateStarredGroupOperandSource_never_incoherentCore
    (model : FlatModel) (declaringGroup : GroupPath)
    (source : SurfaceStarGroupPath) :
    elaborateStarredGroupOperandSource model declaringGroup source ≠
      .error .incoherentCore := by
  unfold elaborateStarredGroupOperandSource
  split
  · simp
  · split
    · rename_i baseError _
      cases baseError <;> simp [StarredGroupBaseError.toElabError]
    · rename_i basePath _
      simp only
      split
      · have dead :=
          elaborateStarredGroupSource_never_incoherentCore
            model declaringGroup source
        cases hSource :
            elaborateStarredGroupSource model declaringGroup source <;>
          simp_all [Except.map]
      · split
        · split
          · simp
          · rename_i plan hPlan
            have ancestry :=
              elaborateStarPathPlan_ancestry model basePath source.groups
                (basePath ++ source.groups.map (·.name)) plan hPlan
            simp [ancestry]
        · simp

/-- The shared planner's dead incoherent branch also remains unreachable through the general starred-group operand elaborator. -/
theorem elaborateStarredGroupOperandSource_never_path_incoherentCore
    (model : FlatModel) (declaringGroup : GroupPath)
    (source : SurfaceStarGroupPath) :
    elaborateStarredGroupOperandSource model declaringGroup source ≠
      .error (.path .incoherentCore) := by
  unfold elaborateStarredGroupOperandSource
  split
  · simp
  · split
    · rename_i baseError _
      cases baseError <;> simp [StarredGroupBaseError.toElabError]
    · rename_i basePath _
      simp only
      split
      · have dead :=
          elaborateStarredGroupSource_never_path_incoherentCore
            model declaringGroup source
        cases hSource :
            elaborateStarredGroupSource model declaringGroup source <;>
          simp_all [Except.map]
      · split
        · split
          · rename_i error hPlan
            have dead :=
              elaborateStarPathPlan_never_incoherentCore
                model basePath source.groups
                  (basePath ++ source.groups.map (·.name))
            rw [hPlan] at dead
            simp only [ne_eq, Except.error.injEq] at dead
            simp [dead]
          · split <;> simp
        · simp

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
