import A12Kernel.Elaboration.CurrentRepetitionStringToNumber

/-! # CurrentRepetition String-to-Number cascade laws -/

namespace A12Kernel

/-- Analyze preserves the exact structural group and the two typed field edges in execution order. -/
@[simp]
theorem checkedCurrentRepetitionStringToNumberCascade_analyze
    (plan : CheckedCurrentRepetitionStringToNumberCascade model) :
    plan.analyze = {
      structuralGroup := plan.source.path
      scope := plan.source.completeScope
      fieldDependencies := [
        (plan.string.targetField, [plan.string.sourceDeclaration.id]),
        (plan.number.placement.targetField,
          [plan.number.placement.sourceDeclaration.id])]
    } := by
  rfl

/-- The fixed inverse cross-family result delegates each already-sourced phase to its established family carrier. -/
theorem checkedCurrentRepetitionStringToNumberCascade_executeResult_projects
    (plan : CheckedCurrentRepetitionStringToNumberCascade model)
    (patterns : PreparedFlatStringPatterns model compilePattern)
    (input : CheckedDocument model)
    (numberPayloadAt : CellAddr → NumberPayload)
    (numberMessages : List (ComputationFormalMessage NumberPayload))
    (stringResidualMessages : List StringResidual)
    (outcomes : CurrentRepetitionStringToNumberOutcomes)
    (evaluated : plan.execute patterns input = .ok outcomes) :
    plan.executeResult patterns input numberPayloadAt numberMessages
        stringResidualMessages =
      .ok {
        string := StringComputationRunView.fromSourcedOutcomes
          stringResidualMessages (outcomes.rows.map (·.string))
        number := NumericComputationRunView.fromSourceOutcomesWithMessages
          MessagePointer.ofCellAddr numberPayloadAt numberMessages
          (outcomes.rows.map (·.number))
      } := by
  rw [CheckedCurrentRepetitionStringToNumberCascade.executeResult, evaluated]
  rfl

end A12Kernel
