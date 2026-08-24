import A12Kernel.Elaboration.RepeatableNumberAggregateCascade

/-! # Repeatable Number to aggregate cascade laws -/

namespace A12Kernel

/-- Analyze preserves the row computation and later aggregate dependency in supplied order. -/
@[simp]
theorem checkedRepeatableNumberAggregateCascade_analyze
    (plan : CheckedRepeatableNumberAggregateCascade model) :
    plan.analyze = {
      producer := plan.row.kind
      operation := plan.operation
      repeatableScope :=
        plan.row.targetDeclaration.repeatableScope
      fieldDependencies := [
        (plan.row.targetField, plan.row.sourceFields),
        (plan.total.operation.core.target.id,
          [plan.row.targetField])]
    } := by
  rfl

end A12Kernel
