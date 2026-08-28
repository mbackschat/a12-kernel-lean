import A12Kernel.Elaboration.ScalarComputationFormalInput
import A12Kernel.Proofs.ComputationFormalInput
import A12Kernel.Proofs.ScalarComputationRun
import A12Kernel.Proofs.ScalarComputationRunResult

/-! # Finite mixed scalar formal-input laws -/

namespace A12Kernel

/-- The mixed whole-call projection retains every checked target in the certified execution order. -/
@[simp] theorem scalarComputationRun_formalInputOperations_targets
    (run : CheckedScalarComputationRun model) :
    run.formalInputOperations.map Prod.fst = run.targetFields := by
  unfold CheckedScalarComputationRun.formalInputOperations
  unfold CheckedScalarComputationRun.targetFields
  rw [List.map_map]
  change (analyzeScalarComputationSteps run.steps).map
      (fun analysis => analysis.targetField) =
    run.steps.map (fun step => step.targetField)
  exact analyzeScalarComputationSteps_targets run.steps

/-- Successful whole-call composition preserves the exact mixed result beside the complete eager inventory. -/
theorem scalarComputationRun_executeResultWithFormalInputs_exact
    (run : CheckedScalarComputationRun model)
    (world : World)
    (patterns : PreparedFlatStringPatterns model compilePattern)
    (input : CheckedDocument model)
    (numberPayloadAt : FieldId → NumberPayload)
    (numberMessages : List (ComputationFormalMessage NumberPayload))
    (stringResidualMessages : List StringResidual)
    (plan : CheckedComputationFormalInputPlan model)
    (result : ScalarComputationRunView StringResidual NumberPayload)
    (planned : run.formalInputPlan = .ok plan)
    (executed : run.executeResult world patterns input numberPayloadAt
      numberMessages stringResidualMessages = .ok result) :
    run.executeResultWithFormalInputs world patterns input numberPayloadAt
      numberMessages stringResidualMessages = .ok
        (ScalarComputationFormalInputRunView.of result (plan.findings input)) := by
  rw [CheckedScalarComputationRun.executeResultWithFormalInputs, planned]
  simp only [Except.mapError, bind, Except.bind, executed]

/-- A mixed execution or result fault retains the exact eager inventory and unchanged typed cause. -/
theorem scalarComputationRun_executeResultWithFormalInputs_failure_exact
    (run : CheckedScalarComputationRun model)
    (world : World)
    (patterns : PreparedFlatStringPatterns model compilePattern)
    (input : CheckedDocument model)
    (numberPayloadAt : FieldId → NumberPayload)
    (numberMessages : List (ComputationFormalMessage NumberPayload))
    (stringResidualMessages : List StringResidual)
    (plan : CheckedComputationFormalInputPlan model)
    (fault : ScalarComputationRunResultFault)
    (planned : run.formalInputPlan = .ok plan)
    (executed : run.executeResult world patterns input numberPayloadAt
      numberMessages stringResidualMessages = .error fault) :
    run.executeResultWithFormalInputs world patterns input numberPayloadAt
      numberMessages stringResidualMessages =
        .error (.execution (plan.findings input) fault) := by
  rw [CheckedScalarComputationRun.executeResultWithFormalInputs, planned]
  simp only [Except.mapError, bind, Except.bind, executed]

end A12Kernel
