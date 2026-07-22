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

end A12Kernel
