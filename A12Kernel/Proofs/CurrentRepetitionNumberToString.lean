import A12Kernel.Elaboration.CurrentRepetitionNumberToString

/-! # CurrentRepetition Number-to-String cascade laws -/

namespace A12Kernel

/-- Analyze preserves the exact structural group and the two typed field edges in execution order. -/
@[simp]
theorem checkedCurrentRepetitionNumberToStringCascade_analyze
    (plan : CheckedCurrentRepetitionNumberToStringCascade model) :
    plan.analyze = {
      structuralGroup := plan.source.path
      scope := plan.source.completeScope
      fieldDependencies := [
        (plan.number.placement.targetField,
          [plan.number.placement.sourceDeclaration.id]),
        (plan.string.targetField, [plan.string.sourceDeclaration.id])]
    } := by
  rfl

/-- The fixed cross-family result delegates each already-sourced phase to its established family carrier. -/
theorem checkedCurrentRepetitionNumberToStringCascade_executeResult_projects
    (plan : CheckedCurrentRepetitionNumberToStringCascade model)
    (patterns : PreparedFlatStringPatterns model compilePattern)
    (input : CheckedDocument model)
    (numberPayloadAt : CellAddr → NumberPayload)
    (numberMessages : List (ComputationFormalMessage NumberPayload))
    (stringResidualMessages : List StringResidual)
    (outcomes : CurrentRepetitionNumberToStringOutcomes)
    (evaluated : plan.execute patterns input = .ok outcomes) :
    plan.executeResult patterns input numberPayloadAt numberMessages
        stringResidualMessages =
      .ok {
        number := NumericComputationRunView.fromSourceOutcomesWithMessages
          MessagePointer.ofCellAddr numberPayloadAt numberMessages
          (outcomes.rows.map (·.number))
        string := StringComputationRunView.fromSourcedOutcomes
          stringResidualMessages (outcomes.rows.map (·.string))
      } := by
  rw [CheckedCurrentRepetitionNumberToStringCascade.executeResult, evaluated]
  rfl

end A12Kernel
