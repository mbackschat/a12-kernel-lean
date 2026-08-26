import A12Kernel.Elaboration.CurrentRepetitionAlternatingChain

/-! # CurrentRepetition alternating Number/String chain laws -/

namespace A12Kernel

/-- Analyze preserves the exact structural group and all three typed field edges in execution order. -/
@[simp]
theorem checkedCurrentRepetitionAlternatingChain_analyze
    (plan : CheckedCurrentRepetitionAlternatingChain model) :
    plan.analyze = {
      structuralGroup := plan.numberToString.source.path
      scope := plan.numberToString.source.completeScope
      fieldDependencies := [
        (plan.numberToString.number.placement.targetField,
          [plan.numberToString.number.placement.sourceDeclaration.id]),
        (plan.numberToString.string.targetField,
          [plan.numberToString.string.sourceDeclaration.id]),
        (plan.third.placement.targetField,
          [plan.third.placement.sourceDeclaration.id])]
    } := by
  rfl

/-- The alternating result delegates its exact String phase and both exact Number phases to the established family carriers. -/
theorem checkedCurrentRepetitionAlternatingChain_executeResult_projects
    (plan : CheckedCurrentRepetitionAlternatingChain model)
    (patterns : PreparedFlatStringPatterns model compilePattern)
    (input : CheckedDocument model)
    (numberPayloadAt : CellAddr → NumberPayload)
    (numberMessages : List (ComputationFormalMessage NumberPayload))
    (stringResidualMessages : List StringResidual)
    (outcomes : CurrentRepetitionAlternatingChainOutcomes)
    (evaluated : plan.execute patterns input = .ok outcomes) :
    plan.executeResult patterns input numberPayloadAt numberMessages
        stringResidualMessages =
      .ok {
        string := StringComputationRunView.fromSourcedOutcomes
          stringResidualMessages (outcomes.rows.map (·.second))
        number := NumericComputationRunView.fromSourceOutcomesWithMessages
          MessagePointer.ofCellAddr numberPayloadAt numberMessages
          (outcomes.rows.flatMap fun row => [row.first, row.third])
      } := by
  rw [CheckedCurrentRepetitionAlternatingChain.executeResult, evaluated]
  rfl

end A12Kernel
