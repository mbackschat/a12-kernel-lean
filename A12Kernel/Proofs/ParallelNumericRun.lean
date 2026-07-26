import A12Kernel.Elaboration.ParallelNumericRun

/-! # Checked parallel Number run-overlay laws -/

namespace A12Kernel

theorem parallelNumericRun_read_pending
    (run : CheckedParallelNumericRun model)
    (state : ParallelNumericRunState) (input : CheckedDocument model)
    (address : CellAddr) (target : address.field ∈ run.targetFields)
    (pending : state.find? address = none) :
    run.readPolicy state input address =
      .ok (NumericDependencyCell.ofObservation .empty).checked := by
  simp [CheckedParallelNumericRun.readPolicy, target, pending]

theorem parallelNumericRun_read_completed
    (run : CheckedParallelNumericRun model)
    (state : ParallelNumericRunState) (input : CheckedDocument model)
    (address : CellAddr) (completion : ParallelNumericDirectOutcome)
    (target : address.field ∈ run.targetFields)
    (found : state.find? address = some completion) :
    run.readPolicy state input address =
      .ok (NumericDependencyCell.ofOutcome completion.outcome).checked := by
  simp [CheckedParallelNumericRun.readPolicy, target, found]

theorem parallelNumericRun_read_input
    (run : CheckedParallelNumericRun model)
    (state : ParallelNumericRunState) (input : CheckedDocument model)
    (address : CellAddr) (ordinary : address.field ∉ run.targetFields) :
    run.readPolicy state input address = input.read address := by
  simp [CheckedParallelNumericRun.readPolicy, ordinary]

/-- Successful execution is exactly the producer result followed by the consumer result evaluated through that completed producer overlay. -/
theorem parallelNumericRun_execute_stages
    (run : CheckedParallelNumericRun model)
    (preliminary : CheckedIndexPreliminary model)
    (producerOutcomes consumerOutcomes :
      List ParallelNumericDirectOutcome)
    (producerExecuted :
      run.producer.executeWithRead preliminary
        (run.readPolicy {} preliminary.base) =
          .ok producerOutcomes)
    (consumerExecuted :
      run.consumer.executeWithRead preliminary
        (run.readPolicy { completed := producerOutcomes }
          preliminary.base) =
          .ok consumerOutcomes) :
    run.execute preliminary =
      .ok (producerOutcomes ++ consumerOutcomes) := by
  simp [CheckedParallelNumericRun.execute, producerExecuted,
    consumerExecuted]

/-- Whole-run result construction delegates the successful addressed outcomes to the existing repeatable Number classifier. -/
theorem parallelNumericRun_executeResult_classifies
    (run : CheckedParallelNumericRun model)
    (preliminary : CheckedIndexPreliminary model)
    (residualMessages : List ResidualMessage)
    (outcomes : List ParallelNumericDirectOutcome)
    (view : NumericComputationRunView ResidualMessage CellAddr)
    (executed : run.execute preliminary = .ok outcomes)
    (classified :
      classifyParallelNumericOutcomes preliminary run.operandRoutes
        residualMessages outcomes = .ok view) :
    run.executeResult preliminary residualMessages = .ok view := by
  simp [CheckedParallelNumericRun.executeResult, executed, classified]

end A12Kernel
