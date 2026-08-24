import A12Kernel.Elaboration.RepeatableNumberAggregateCascade

/-! # Repeatable Number to aggregate cascade laws -/

namespace A12Kernel

/-- Analyze preserves the row computation and later aggregate dependency in supplied order. -/
@[simp]
theorem checkedRepeatableNumberAggregateCascade_analyze
    (plan : CheckedRepeatableNumberAggregateCascade model) :
    plan.analyze = {
      producer := plan.row.kind
      consumer := plan.consumer.kind
      operation := plan.operation
      repeatableScope :=
        plan.row.targetDeclaration.repeatableScope
      fieldDependencies := [
        (plan.row.targetField, plan.row.sourceFields),
        (plan.total.operation.core.target.id,
          plan.consumer.fieldDependencies)]
    } := by
  rfl

/-- Analyze extends the checked row-to-aggregate prefix with exactly one deduplicated scalar field edge. -/
@[simp]
theorem checkedRepeatableNumberAggregateScalarCascade_analyze
    (plan : CheckedRepeatableNumberAggregateScalarCascade model) :
    plan.analyze = {
      cascade := plan.cascade.analyze
      scalarOperation := plan.scalarOperation
      fieldDependencies := plan.cascade.analyze.fieldDependencies ++ [
        (plan.scalar.operation.core.target.id,
          [plan.leftDeclaration.id, plan.rightDeclaration.id].eraseDups)]
    } := by
  rfl

end A12Kernel
