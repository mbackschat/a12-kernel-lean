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
  simp [CheckedStarFieldPath.bindingScope]

/-- Full validation always supplies complete all-rows relevance. -/
@[simp] theorem checkedStarFieldPath_allRowsRelevant_full
    (checked : CheckedStarFieldPath model) :
    checked.allRowsRelevant .full = true := by
  rfl

/-- Partial all-rows relevance requires one independently covering entity; a union of concrete non-covering entries is not upgraded to a wildcard. -/
theorem checkedStarFieldPath_allRowsRelevant_partialSet_iff
    (checked : CheckedStarFieldPath model) (entities : List RelevantEntityPattern) :
    checked.allRowsRelevant (.partialSet entities) = true ↔
      ∃ entity ∈ entities,
        entity.coversAllRows model checked.declaration.path = true := by
  simp [CheckedStarFieldPath.allRowsRelevant,
    ValidationRelevanceScope.coversAllRows]

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

end A12Kernel
