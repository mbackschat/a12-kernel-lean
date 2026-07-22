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

end A12Kernel
