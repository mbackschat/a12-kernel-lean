import A12Kernel.Elaboration.RepeatableNumberAggregateCascade

/-! # Repeatable Number to aggregate cascade laws -/

namespace A12Kernel

/-- Analyze preserves the row computation and later aggregate dependency in supplied order. -/
@[simp]
theorem checkedRepeatableNumberAggregateCascade_analyze
    (plan : CheckedRepeatableNumberAggregateCascade model) :
    plan.analyze = {
      operation := plan.operation
      repeatableScope :=
        plan.row.placement.targetDeclaration.repeatableScope
      fieldDependencies := [
        (plan.row.placement.targetField,
          [plan.row.placement.sourceDeclaration.id]),
        (plan.total.operation.core.target.id,
          [plan.row.placement.targetField])]
    } := by
  rfl

end A12Kernel
