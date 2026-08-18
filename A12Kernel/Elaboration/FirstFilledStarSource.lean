import A12Kernel.Elaboration.StarPath

/-! # Checked starred source shapes for `FirstFilledValue` computation -/

namespace A12Kernel.CheckedStarFieldPath

/-- Whether this checked field is declared directly in exactly one reopened repeatable group. This is the shared bounded shape used by scalar `FirstFilledValue` computation carriers. -/
def isDirectSingleStar (checked : CheckedStarFieldPath model) : Bool :=
  match checked.path.axes, checked.declaration.repeatableScope with
  | [axis], [level] =>
      checked.path.firstStar == 0 && axis.level == level &&
        model.repeatableGroups.any fun group =>
          group.level == level && group.path == checked.declaration.groupPath
  | _, _ => false

end A12Kernel.CheckedStarFieldPath
