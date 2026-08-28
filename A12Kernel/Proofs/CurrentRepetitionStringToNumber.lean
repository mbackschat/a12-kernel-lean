import A12Kernel.Elaboration.CurrentRepetitionStringToNumber
import A12Kernel.Proofs.ComputationFormalInput

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

/-- A prepared first-phase read preserves the Number formal-text cell and adds only the selected generated finding annotation. -/
theorem currentRepetitionStringToNumber_preparedStringSourceRead_exact
    (preliminary : CheckedIndexPreliminary model)
    (address : CellAddr) (base : CheckedCell)
    (read : CheckedAddressedFieldValueAsString.readSource preliminary.base
      address = .ok base) :
    CheckedCurrentRepetitionStringToNumberCascade.preparedStringSourceRead
      preliminary address = .ok (preliminary.annotateCell address base) := by
  rw [CheckedCurrentRepetitionStringToNumberCascade.preparedStringSourceRead,
    read]
  rfl

/-- Caller-supplied first-phase state feeds only the String producer before the established exact String dependency overlay reaches Number. -/
theorem checkedCurrentRepetitionStringToNumberCascade_executeWithRead_delegates
    (plan : CheckedCurrentRepetitionStringToNumberCascade model)
    (patterns : PreparedFlatStringPatterns model compilePattern)
    (input : CheckedDocument model)
    (read : CellAddr → Except CheckedDocumentError CheckedCell) :
    plan.executeWithRead patterns input read = (do
      let string ← plan.executeStringPhaseWithRead patterns input read
      let number ← plan.executeNumberPhase input string
      pure (CheckedCurrentRepetitionStringToNumberCascade.assemblePhases
        string number)) := by
  rfl

/-- Whole-call findings remain global while both typed phase views project the exact prepared execution once. -/
theorem currentRepetitionStringToNumber_executeResultWithFormalInputs_exact
    (plan : CheckedCurrentRepetitionStringToNumberCascade model)
    (patterns : PreparedFlatStringPatterns model compilePattern)
    (input : CheckedDocument model)
    (inputPlan : CheckedComputationFormalInputPlan model)
    (prepared : ComputationFormalInputPreparation model)
    (outcomes : CurrentRepetitionStringToNumberOutcomes)
    (view : CurrentRepetitionStringToNumberFormalInputRunView model)
    (planned : plan.formalInputPlan = .ok inputPlan)
    (preparation : inputPlan.prepare input = .ok prepared)
    (executed : plan.executeWithRead patterns input
      (CheckedCurrentRepetitionStringToNumberCascade.preparedStringSourceRead
        prepared.preliminary) = .ok outcomes)
    (produced : plan.executeResultWithFormalInputs patterns input = .ok view) :
    view.formalErrorsInOperands = prepared.formalErrorsInOperands ∧
      view.phases.string = StringComputationRunView.fromSourcedOutcomes []
        (outcomes.rows.map (·.string)) ∧
      view.phases.number =
        NumericComputationRunView.fromSourceOutcomesWithMessages
          MessagePointer.ofCellAddr (fun _ => ()) []
          (outcomes.rows.map (·.number)) := by
  rw [CheckedCurrentRepetitionStringToNumberCascade.executeResultWithFormalInputs,
    planned] at produced
  simp only [bind, Except.bind, Except.mapError, preparation] at produced
  rw [CheckedCurrentRepetitionStringToNumberCascade.executeResultWithRead,
    executed] at produced
  simp only [bind, Except.bind, pure, Except.pure,
    Except.ok.injEq] at produced
  subst view
  exact ⟨rfl, rfl, rfl⟩

/-- A post-preparation inverse-cascade failure retains the exact eager inventory beside the unchanged typed fault. -/
theorem currentRepetitionStringToNumber_executeResultWithFormalInputs_failure_exact
    (plan : CheckedCurrentRepetitionStringToNumberCascade model)
    (patterns : PreparedFlatStringPatterns model compilePattern)
    (input : CheckedDocument model)
    (inputPlan : CheckedComputationFormalInputPlan model)
    (prepared : ComputationFormalInputPreparation model)
    (fault : CurrentRepetitionStringToNumberFault)
    (planned : plan.formalInputPlan = .ok inputPlan)
    (preparation : inputPlan.prepare input = .ok prepared)
    (executed : plan.executeResultWithRead patterns input
      (CheckedCurrentRepetitionStringToNumberCascade.preparedStringSourceRead
        prepared.preliminary) (fun _ => ()) []
      ([] : List ComputationFormalInputFinding) = .error fault) :
    plan.executeResultWithFormalInputs patterns input =
      .error (.execution prepared.formalErrorsInOperands fault) := by
  rw [CheckedCurrentRepetitionStringToNumberCascade.executeResultWithFormalInputs,
    planned]
  simp only [bind, Except.bind, Except.mapError, preparation, executed]

end A12Kernel
