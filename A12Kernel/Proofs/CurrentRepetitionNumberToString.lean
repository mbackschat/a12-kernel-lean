import A12Kernel.Elaboration.CurrentRepetitionNumberToString

/-! # CurrentRepetition Number-to-String cascade laws -/

namespace A12Kernel

/-- Analyze preserves the exact structural group and the two typed field edges in execution order. -/
@[simp]
theorem checkedCurrentRepetitionNumberToStringCascade_analyze
    (plan : CheckedCurrentRepetitionNumberToStringCascade model) :
    plan.analyze = {
      structuralGroup := plan.source.path
      scope := [plan.source.group.level]
      fieldDependencies := [
        (plan.number.placement.targetField,
          [plan.number.placement.sourceDeclaration.id]),
        (plan.string.targetField, [plan.string.sourceDeclaration.id])]
    } := by
  rfl

end A12Kernel
