import A12Kernel.Elaboration.CurrentRepetitionStringToNumber

/-! # CurrentRepetition String-to-Number cascade laws -/

namespace A12Kernel

/-- Analyze preserves the exact structural group and the two typed field edges in execution order. -/
@[simp]
theorem checkedCurrentRepetitionStringToNumberCascade_analyze
    (plan : CheckedCurrentRepetitionStringToNumberCascade model) :
    plan.analyze = {
      structuralGroup := plan.source.path
      scope := [plan.source.group.level]
      fieldDependencies := [
        (plan.string.targetField, [plan.string.sourceDeclaration.id]),
        (plan.number.placement.targetField,
          [plan.number.placement.sourceDeclaration.id])]
    } := by
  rfl

end A12Kernel
