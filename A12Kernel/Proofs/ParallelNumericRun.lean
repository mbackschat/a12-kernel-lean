import A12Kernel.Elaboration.ParallelNumericRun
import A12Kernel.Proofs.ComputationRunPlan
import A12Kernel.Proofs.FieldId

/-! # Checked parallel Number run-overlay laws -/

namespace A12Kernel

theorem checkedParallelNumericPlan_targetFields_nodup
    (plan : CheckedParallelNumericPlan model) :
    plan.targetFields.Nodup := by
  exact (fieldId_firstDuplicate_none_iff_nodup _).mp
    plan.uniqueTargets

/-- A certified table cannot read the target of any later supplied table. This no-later-read result is the exact dependency-order guarantee; self-reference is outside the finite-plan certificate. -/
theorem checkedParallelNumericPlan_references_later_false
    (plan : CheckedParallelNumericPlan model)
    (earlier later :
      List (CheckedParallelNumericAlternativeTable model))
    (consumer producer : CheckedParallelNumericAlternativeTable model)
    (split : plan.tables = earlier ++ consumer :: later)
    (member : producer ∈ later) :
    consumer.referencesField producer.targetField = false := by
  have ordered :
      firstForwardComputationDependency?
        (·.targetField) (·.referencesField ·) plan.tables = none := by
    simpa [firstForwardParallelNumericDependency?] using
      plan.dependenciesOrdered
  rw [split] at ordered
  have suffix :=
    firstForwardComputationDependency_none_suffix
      (·.targetField) (·.referencesField ·)
      earlier (consumer :: later) ordered
  exact firstForwardComputationDependency_none_head
    (·.targetField) (·.referencesField ·)
    consumer later suffix producer member

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
