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

/-- Successful whole-call composition admits diagnostics before projecting the retained raw outcomes. -/
theorem scalarComputationRun_executeResultWithFormalInputs_exact
    (run : CheckedScalarComputationRun model) (world : World)
    (patterns : PreparedFlatStringPatterns model compilePattern) (input : CheckedDocument model)
    (numberPayloadAt : FieldId → NumberPayload)
    (numberMessages : List (ComputationFormalMessage NumberPayload))
    (stringResidualMessages : List StringResidual)
    (plan : CheckedComputationFormalInputPlan model)
    (prepared : ComputationFormalInputPreparation model) (outcomes : List ScalarComputationOutcome)
    (result : ScalarComputationRunView StringResidual NumberPayload)
    (planned : run.formalInputPlan = .ok plan)
    (preparation : plan.prepare input = .ok prepared)
    (executed : run.execute world patterns prepared.preliminary.computationInput = .ok outcomes)
    (assembled : checkComputationReportPointers
      (prepared.formalErrorsInOperands.map (fun finding => MessagePointer.ofCellAddr finding.address) ++
        CheckedScalarComputationRun.numberReportPointers outcomes numberMessages) = .ok ())
    (projected : CheckedScalarComputationRun.resultFromOutcomes input numberPayloadAt
      numberMessages stringResidualMessages outcomes = .ok result) :
    run.executeResultWithFormalInputs world patterns input numberPayloadAt
      numberMessages stringResidualMessages = .ok
        (ScalarComputationFormalInputRunView.of result prepared.formalErrorsInOperands) := by
  simp [CheckedScalarComputationRun.executeResultWithFormalInputs, planned, preparation, executed,
    assembled, projected, Except.mapError, bind, Except.bind, pure, Except.pure]

/-- A source/result projection fault is reached only after successful diagnostic assembly. -/
theorem scalarComputationRun_executeResultWithFormalInputs_failure_exact
    (run : CheckedScalarComputationRun model) (world : World)
    (patterns : PreparedFlatStringPatterns model compilePattern) (input : CheckedDocument model)
    (numberPayloadAt : FieldId → NumberPayload)
    (numberMessages : List (ComputationFormalMessage NumberPayload))
    (stringResidualMessages : List StringResidual)
    (plan : CheckedComputationFormalInputPlan model)
    (prepared : ComputationFormalInputPreparation model) (outcomes : List ScalarComputationOutcome)
    (fault : ScalarComputationRunResultFault)
    (planned : run.formalInputPlan = .ok plan)
    (preparation : plan.prepare input = .ok prepared)
    (executed : run.execute world patterns prepared.preliminary.computationInput = .ok outcomes)
    (assembled : checkComputationReportPointers
      (prepared.formalErrorsInOperands.map (fun finding => MessagePointer.ofCellAddr finding.address) ++
        CheckedScalarComputationRun.numberReportPointers outcomes numberMessages) = .ok ())
    (projected : CheckedScalarComputationRun.resultFromOutcomes input numberPayloadAt
      numberMessages stringResidualMessages outcomes = .error fault) :
    run.executeResultWithFormalInputs world patterns input numberPayloadAt
      numberMessages stringResidualMessages = .error (.execution prepared.formalErrorsInOperands fault) := by
  simp [CheckedScalarComputationRun.executeResultWithFormalInputs, planned, preparation, executed,
    assembled, projected, Except.mapError, bind, Except.bind]

/-- Raw execution faults precede assembly even when the selected input reports collide. -/
theorem scalarComputationRun_executeResultWithFormalInputs_execution_failure_exact
    (run : CheckedScalarComputationRun model) (world : World)
    (patterns : PreparedFlatStringPatterns model compilePattern) (input : CheckedDocument model)
    (numberPayloadAt : FieldId → NumberPayload)
    (numberMessages : List (ComputationFormalMessage NumberPayload))
    (stringResidualMessages : List StringResidual)
    (plan : CheckedComputationFormalInputPlan model)
    (prepared : ComputationFormalInputPreparation model) (fault : ScalarComputationRunFault)
    (planned : run.formalInputPlan = .ok plan)
    (preparation : plan.prepare input = .ok prepared)
    (executed : run.execute world patterns prepared.preliminary.computationInput = .error fault) :
    run.executeResultWithFormalInputs world patterns input numberPayloadAt
      numberMessages stringResidualMessages =
        .error (.execution prepared.formalErrorsInOperands (.execution fault)) := by
  simp [CheckedScalarComputationRun.executeResultWithFormalInputs, planned, preparation, executed,
    Except.mapError, bind, Except.bind]

end A12Kernel
