import A12Kernel.Elaboration.CurrentRepetitionAlternatingChain

/-! # CurrentRepetition alternating Number/String chain laws -/

namespace A12Kernel

/-- Analyze preserves the exact structural group and all three typed field edges in execution order. -/
@[simp]
theorem checkedCurrentRepetitionAlternatingChain_analyze
    (plan : CheckedCurrentRepetitionAlternatingChain model) :
    plan.analyze = {
      structuralGroup := plan.numberToString.source.path
      scope := [plan.numberToString.source.group.level]
      fieldDependencies := [
        (plan.numberToString.number.placement.targetField,
          [plan.numberToString.number.placement.sourceDeclaration.id]),
        (plan.numberToString.string.targetField,
          [plan.numberToString.string.sourceDeclaration.id]),
        (plan.third.placement.targetField,
          [plan.third.placement.sourceDeclaration.id])]
    } := by
  rfl

end A12Kernel
