import A12Kernel.Elaboration.StarPath

namespace A12Kernel

/-- Checked lowering preserves the field declaration's exact outer-to-inner repeatable ancestry. -/
@[simp] theorem checkedStarFieldPath_ancestry (checked : CheckedStarFieldPath model) :
    checked.path.axes.map (·.level) = checked.declaration.repeatableScope :=
  checked.ancestryOwned

/-- Every checked star path reopens an actual repeatable axis. -/
theorem checkedStarFieldPath_firstStar_lt (checked : CheckedStarFieldPath model) :
    checked.path.firstStar < checked.path.axes.length :=
  checked.firstStarWithin

/-- The checked binding scope is exactly the declaration ancestry strictly above the first star. -/
theorem checkedStarFieldPath_bindingScope
    (checked : CheckedStarFieldPath model) :
    checked.bindingScope =
      checked.declaration.repeatableScope.take checked.path.firstStar := by
  rw [← checked.ancestryOwned]
  simp [CheckedStarFieldPath.bindingScope, StarPath.bindingScope]

/-- Full validation always supplies complete all-rows relevance. -/
@[simp] theorem checkedStarFieldPath_allRowsRelevant_full
    (checked : CheckedStarFieldPath model) (outer : Env) :
    checked.allRowsRelevant .full outer = true := by
  rfl

/-- Full validation always supplies the value-list extent's covering identifier. -/
@[simp] theorem checkedStarFieldPath_valueListExtentRelevant_full
    (checked : CheckedStarFieldPath model) (outer : Env) :
    checked.valueListExtentRelevant .full outer = true := by
  rfl

/-- Partial all-rows relevance is universal over the normalized identifiers retained in the current iteration subtree. A broader wildcard removes identifiers that it encompasses before this gate. -/
theorem checkedStarFieldPath_allRowsRelevant_partialSet_iff
    (checked : CheckedStarFieldPath model) (entities : List RelevantEntityPattern)
    (outer : Env) :
    let retained := ValidationRelevanceScope.aggregateExtentPatterns entities model
      checked.declaration.path checked.bindingScope outer
    checked.allRowsRelevant (.partialSet entities) outer = true ↔
      retained ≠ [] ∧ ∀ entity ∈ retained,
        entity.wildcardsLevels model checked.reopenedScope = true := by
  simp [CheckedStarFieldPath.allRowsRelevant,
    ValidationRelevanceScope.coversAggregateExtent]

/-- Partial value-list extent relevance is existential: one covering identifier suffices even when concrete siblings are also selected. -/
theorem checkedStarFieldPath_valueListExtentRelevant_partialSet_iff
    (checked : CheckedStarFieldPath model) (entities : List RelevantEntityPattern)
    (outer : Env) :
    checked.valueListExtentRelevant (.partialSet entities) outer = true ↔
      ∃ entity ∈ entities,
        entity.coversValueListExtent model checked.declaration.path
          checked.bindingScope checked.reopenedScope outer = true := by
  simp [CheckedStarFieldPath.valueListExtentRelevant,
    ValidationRelevanceScope.coversValueListExtent]

/-- The compatibility boundary retained by unmeasured count consumers remains exactly existential over one target-or-ancestor identifier whose named repeatable prefixes are wildcarded. -/
theorem checkedStarFieldPath_singleEntityExtentRelevant_partialSet_iff
    (checked : CheckedStarFieldPath model) (entities : List RelevantEntityPattern) :
    checked.singleEntityExtentRelevant (.partialSet entities) = true ↔
      ∃ entity ∈ entities,
        entity.coversSingleEntityExtent model checked.declaration.path = true := by
  simp [CheckedStarFieldPath.singleEntityExtentRelevant,
    ValidationRelevanceScope.coversSingleEntityExtent]

/-- Full validation makes every concrete instance of a checked star relevant. -/
@[simp] theorem checkedStarFieldPath_cellRelevant_full
    (checked : CheckedStarFieldPath model) (environment : Env) :
    checked.cellRelevant .full environment = true := by
  rfl

/-- Partial per-cell relevance is ordinary existential coverage; unlike the all-rows gate, separate concrete entities may cover separate instances. -/
theorem checkedStarFieldPath_cellRelevant_partialSet_iff
    (checked : CheckedStarFieldPath model) (entities : List RelevantEntityPattern)
    (environment : Env) :
    checked.cellRelevant (.partialSet entities) environment = true ↔
      ∃ entity ∈ entities,
        entity.coversCell model checked.declaration.path environment = true := by
  simp [CheckedStarFieldPath.cellRelevant,
    ValidationRelevanceScope.coversCell]

/-- Global augmentation makes a model-owned global declaration relevant at every concrete environment covered by its all-instances pattern, independently of the caller's partial set. -/
theorem validationRelevanceScope_withGlobals_covers_global
    (scope : ValidationRelevanceScope) (model : FlatModel)
    (declaration : FlatFieldDecl) (environment : Env)
    (lookup : model.lookupUniqueId declaration.id = .ok declaration)
    (owned : declaration ∈ model.fields)
    (global : declaration.isGlobal = true)
    (covered :
      (RelevantEntityPattern.allInstances declaration.path).coversCell
        model declaration.path environment = true) :
    (scope.withGlobals model).coversField
      model declaration.id environment = true := by
  cases scope with
  | full =>
      simp [ValidationRelevanceScope.withGlobals,
        ValidationRelevanceScope.coversField, lookup,
        ValidationRelevanceScope.coversCell]
  | partialSet entities =>
      simp [ValidationRelevanceScope.withGlobals,
        ValidationRelevanceScope.coversField, lookup,
        ValidationRelevanceScope.coversCell, List.any_append]
      exact .inr ⟨declaration, owned, global, covered⟩

/-- Full validation makes every group instance completely relevant without inspecting model descendants. -/
@[simp] theorem validationRelevanceScope_groupRelevance_full
    (model : FlatModel) (groupPath : GroupPath) (environment : Env) :
    ValidationRelevanceScope.full.groupRelevance
      model groupPath environment = .fullyRelevant := by
  rfl

/-- An empty partial selection cannot make any group instance relevant. -/
@[simp] theorem validationRelevanceScope_groupRelevance_empty
    (model : FlatModel) (groupPath : GroupPath) (environment : Env) :
    (ValidationRelevanceScope.partialSet []).groupRelevance
      model groupPath environment = .noneRelevant := by
  rfl

end A12Kernel
