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

theorem parallelNumericPlan_read_pending
    (plan : CheckedParallelNumericPlan model)
    (state : ParallelNumericRunState) (input : CheckedDocument model)
    (address : CellAddr) (target : address.field ∈ plan.targetFields)
    (pending : state.find? address = none) :
    plan.readPolicy state input address =
      .ok (NumericDependencyCell.ofObservation .empty).checked := by
  simp [CheckedParallelNumericPlan.readPolicy, target, pending]

theorem parallelNumericPlan_read_completed
    (plan : CheckedParallelNumericPlan model)
    (state : ParallelNumericRunState) (input : CheckedDocument model)
    (address : CellAddr) (completion : ParallelNumericDirectOutcome)
    (target : address.field ∈ plan.targetFields)
    (found : state.find? address = some completion) :
    plan.readPolicy state input address =
      .ok (NumericDependencyCell.ofOutcome completion.outcome).checked := by
  simp [CheckedParallelNumericPlan.readPolicy, target, found]

theorem parallelNumericPlan_read_input
    (plan : CheckedParallelNumericPlan model)
    (state : ParallelNumericRunState) (input : CheckedDocument model)
    (address : CellAddr) (ordinary : address.field ∉ plan.targetFields) :
    plan.readPolicy state input address = input.read address := by
  simp [CheckedParallelNumericPlan.readPolicy, ordinary]

/-- Successful execution of a prefix composes exactly with any remaining supplied suffix. -/
theorem parallelNumericPlan_executeTables_append
    (plan : CheckedParallelNumericPlan model)
    (preliminary : CheckedIndexPreliminary model)
    (left right :
      List (CheckedParallelNumericAlternativeTable model))
    (state mid : ParallelNumericRunState)
    (first :
      plan.executeTables preliminary left state = .ok mid) :
    plan.executeTables preliminary (left ++ right) state =
      plan.executeTables preliminary right mid := by
  induction left generalizing state mid with
  | nil =>
      simp [CheckedParallelNumericPlan.executeTables] at first
      subst mid
      rfl
  | cons table remaining ih =>
      cases executed :
          table.executeWithRead preliminary
            (plan.readPolicy state preliminary.base) with
      | error error =>
          simp [CheckedParallelNumericPlan.executeTables, executed] at first
      | ok outcomes =>
          simp only [CheckedParallelNumericPlan.executeTables, executed,
            List.cons_append] at first ⊢
          exact ih _ _ first

/-- Whole-run result construction delegates the successful addressed outcomes to the existing repeatable Number classifier. -/
theorem parallelNumericPlan_executeResult_classifies
    (plan : CheckedParallelNumericPlan model)
    (preliminary : CheckedIndexPreliminary model)
    (residualMessages : List ResidualMessage)
    (outcomes : List ParallelNumericDirectOutcome)
    (view : NumericComputationRunView ResidualMessage CellAddr)
    (executed : plan.execute preliminary = .ok outcomes)
    (classified :
      classifyParallelNumericOutcomes preliminary plan.operandRoutes
        residualMessages outcomes = .ok view) :
    plan.executeResult preliminary residualMessages = .ok view := by
  simp [CheckedParallelNumericPlan.executeResult, executed, classified]

end A12Kernel
