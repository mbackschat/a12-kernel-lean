import A12Kernel.Elaboration.RepeatableNumberAggregateMixedRun

/-! # Aggregate-seeded mixed scalar-run laws -/

namespace A12Kernel

/-- Analyze retains every suffix family, target, and computed-target edge in supplied order. -/
@[simp]
theorem checkedRepeatableNumberAggregateMixedRun_analyze
    (plan : CheckedRepeatableNumberAggregateMixedRun model) :
    plan.analyze =
      let candidates :=
        plan.cascade.total.operation.core.target.id :: plan.run.targetFields
      {
        cascade := plan.cascade.analyze
        scalarTargets := plan.run.steps.map fun step =>
          (step.targetKind, step.targetField)
        computedDependencies := plan.run.steps.map fun step =>
          (step.targetField,
            candidates.filter fun field => step.referencesField field)
      } := by
  rfl

end A12Kernel
