import A12Kernel.Elaboration.NumberEntityList
import A12Kernel.Elaboration.TokenDistinctCount
import A12Kernel.Elaboration.TemporalDistinctCount

namespace A12Kernel

/-- The typed overload of one distinct count, shared by validation and computation expressions. -/
inductive CheckedDistinctCountSource (model : FlatModel) where
  | number (source : CheckedNumberEntitySource model)
  | token (source : CheckedTokenEntitySource model)
  | temporal (run : CheckedTemporalDistinctCountRun model)

/-- Select the existing typed carrier without erasing its identity projection. Preserve the
    validation expression carrier's Number refusal when no represented overload accepts. -/
def elaborateDistinctCountSource (model : FlatModel) (declaringGroup : GroupPath)
    (source : SurfaceFieldEntitySource) (fixedTargetGroup? : Option GroupPath := none)
    (bindingGroup? : Option GroupPath := none) :
    Except NumberEntityElabError (CheckedDistinctCountSource model) :=
  -- A count asks the category gate ahead of the list's repeat and root gates on every overload, so
  -- the Number overload, whose refusal stands when none accepts, asks it there too
  -- (k22-static-classes-2026-10-24, `s9-n3`, `s9-n4`).
  match elaborateNumberEntitySource model declaringGroup source
      (fixedTargetGroup? := fixedTargetGroup?)
      (writtenGroup := bindingGroup?.getD declaringGroup) (bindingGroup? := bindingGroup?)
      (categoryGate := .aheadOfRepeat) with
  | .ok checked => pure (.number checked)
  | .error error =>
      match elaborateTokenDistinctCountSource model declaringGroup source
          (fixedTargetGroup? := fixedTargetGroup?) (bindingGroup? := bindingGroup?)
          (writtenGroup := bindingGroup?.getD declaringGroup) with
      | .ok checked => pure (.token checked)
      | .error _ =>
          match (elaborateTemporalDistinctCountSource model declaringGroup source
              (fixedTargetGroup? := fixedTargetGroup?)
              (writtenGroup := bindingGroup?.getD declaringGroup)).toOption.bind
              fun temporal => (checkTemporalDistinctCountRun temporal).toOption with
          | some run => pure (.temporal run)
          | none => throw error

end A12Kernel
