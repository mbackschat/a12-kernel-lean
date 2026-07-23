import A12Kernel.Elaboration.StarNumber
import A12Kernel.Proofs.Correlation

namespace A12Kernel

/-- The concrete Number consumer retains the general checked path's exact model ancestry. -/
@[simp] theorem checkedStarNumberSource_ancestry (checked : CheckedStarNumberSource model) :
    checked.source.path.axes.map (·.level) =
      checked.source.declaration.repeatableScope :=
  checked.source.ancestryOwned

/-- Checked authored filter lowering certifies every Number/repetition leaf against the exact candidate and captured environment levels. -/
theorem checkedStarNumberHavingSource_wellFormed
    (checked : CheckedStarNumberHavingSource model) :
    checked.having.wellFormedForEnvironments model
      (checked.source.source.path.axes.map (·.level)) checked.outerLevels = true :=
  checked.filter.wellFormed

/-- A checked authored filter remains inside the conjunction-only surface fragment even though the resolved filter core also supports `Or`. -/
theorem checkedStarNumberHavingSource_conjunctive
    (checked : CheckedStarNumberHavingSource model) :
    checked.having.isConjunctive = true :=
  checked.filter.authored.conjunctive

/-- A checked authored filter depends on at least one unmarked reference at a level actually reopened by its star. -/
theorem checkedStarNumberHavingSource_reachesReopenedLevel
    (checked : CheckedStarNumberHavingSource model) :
    checked.having.reachesReopenedLevel model
      ((checked.source.source.path.axes.map (·.level)).drop
        checked.source.source.path.firstStar) = true :=
  checked.filter.reachesReopenedLevel

/-- The checked authored wrapper delegates runtime selection to the established resolved environment filter without changing its topology or target classification. -/
theorem checkedStarNumberHavingSource_resolvedValueSide
    (checked : CheckedStarNumberHavingSource model) (document : Document)
    (outer : Env) (filterRead : Env → FieldId → CheckedCell)
    (read : Env → FieldId → RawCell) :
    checked.resolvedValueSide document outer filterRead read =
      checked.source.resolvedValidationHavingValueSide document outer
        checked.having filterRead read := by
  rfl

/-- Structural over-repetition replaces ordinary scalar findings at the checked cell boundary. -/
theorem checkedStarNumberSource_overLimit (checked : CheckedStarNumberSource model)
    (read : Env → FieldId → RawCell) (environment : Env)
    (overLimit : checked.environmentOverLimit environment = true) :
    (checked.checkedCell read environment).parsed = none ∧
      (checked.checkedCell read environment).findings = [.overRepetition] := by
  have sourceOverLimit :
      checked.source.environmentOverLimit environment = true := by
    simpa [CheckedStarNumberSource.environmentOverLimit] using overLimit
  simp [CheckedStarNumberSource.checkedCell,
    CheckedStarFieldPath.checkedCell, CheckedStarFieldPath.contextualizeCell,
    CheckedCell.withOverRepetitionIf, sourceOverLimit]

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
  apply checkedStarFieldPath_havingBeforeClassification
  exact agree

/-- A nonrelevant all-rows source is rejected before target classification, so changing every raw target remains unobservable. -/
theorem checkedStarNumberSource_nonRelevantBeforeTarget
    (checked : CheckedStarNumberSource model) (resolved : ResolvedStarTopology)
    (scope : ValidationRelevanceScope) (left right : Env → FieldId → RawCell)
    (nonRelevant : checked.source.allRowsRelevant scope = false) :
    checked.selectedPartialAllRowsValueSide resolved scope left = .nonRelevant ∧
      checked.selectedPartialAllRowsValueSide resolved scope right = .nonRelevant := by
  simp [CheckedStarNumberSource.selectedPartialAllRowsValueSide, nonRelevant]

/-- All-rows relevance leaves the topology-derived cells and hierarchical omitted-tail marker unchanged. -/
theorem checkedStarNumberSource_relevantPreservesSide
    (checked : CheckedStarNumberSource model) (resolved : ResolvedStarTopology)
    (scope : ValidationRelevanceScope) (read : Env → FieldId → RawCell)
    (relevant : checked.source.allRowsRelevant scope = true) :
    checked.selectedPartialAllRowsValueSide resolved scope read =
      .relevant (resolved.toResolvedSide (checked.valueListCell read)) := by
  simp [CheckedStarNumberSource.selectedPartialAllRowsValueSide, relevant]

end A12Kernel
