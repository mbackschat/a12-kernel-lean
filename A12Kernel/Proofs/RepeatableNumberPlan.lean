import A12Kernel.Elaboration.RepeatableNumberPlan
import A12Kernel.Proofs.ComputationRunPlan
import A12Kernel.Proofs.FieldId

/-! # Authored repeatable Number plan laws

The plan's certificate is sound and complete for cycles by specializing the shared authored-order
laws, and its read overlay never exposes a plan target's stored value.
-/

namespace A12Kernel

/-- A certified plan runs exactly its authored steps, in some order. -/
theorem repeatableNumberPlan_executionSteps_perm (plan : CheckedRepeatableNumberPlan model) :
    plan.execution.Perm plan.authored := by
  rw [plan.executionOrdered]
  exact computationAuthoredOrder_perm _ _ _ _

/-- A plan refused as a cycle has read-closed steps: the refusal never falls on an acyclic plan. -/
theorem certifyRepeatableNumberPlan_cycle_readClosed
    (steps : List (CheckedNumericComputationTable model)) (step reads : FieldId)
    (refused : certifyRepeatableNumberPlan steps = .error (.cycle step reads)) :
    ∃ stuck, ComputationStepsReadClosed CheckedNumericComputationTable.targetField
        (fun table => table.requiresProducer (numericComputationProducerProtection steps)) stuck ∧
      ∀ member ∈ stuck, member ∈ steps := by
  unfold certifyRepeatableNumberPlan at refused
  split at refused
  · simp at refused
  · split at refused
    · simp at refused
    · rename_i noDuplicate
      split at refused
      · rename_i forward
        have unique : (steps.map (·.targetField)).Nodup :=
          (fieldId_firstDuplicate_none_iff_nodup _).mp noDuplicate
        exact computationAuthoredOrder_forward_readClosed _ _ steps.length steps
          (Nat.le_refl _) unique (by rw [forward]; simp)
      · simp at refused

/-- A certified plan's authored steps hold no read-closed steps, so every cyclic plan is refused. -/
theorem repeatableNumberPlan_not_readClosed (plan : CheckedRepeatableNumberPlan model)
    (stuck : List (CheckedNumericComputationTable model))
    (closed : ComputationStepsReadClosed CheckedNumericComputationTable.targetField
      (fun table => table.requiresProducer (numericComputationProducerProtection plan.authored)) stuck) :
    ¬ ∀ member ∈ stuck, member ∈ plan.authored := fun within =>
  computationSteps_not_readClosed _ _ plan.execution stuck plan.dependenciesOrdered closed
    fun member memberStuck =>
      (repeatableNumberPlan_executionSteps_perm plan).mem_iff.mpr (within member memberStuck)

/-- A plan target no completion covers reads clean empty, whatever the document stores there. -/
theorem repeatableNumberPlan_read_pending (plan : CheckedRepeatableNumberPlan model)
    (input : CheckedDocument model) (completed : List (SourcedNumericTargetOutcome CellAddr))
    (address : CellAddr)
    (uncovered : completed.find? (fun outcome => outcome.targetField == address) = none)
    (planned : plan.targetFields.contains address.field = true) :
    plan.read input completed address =
      .ok (NumericDependencyCell.ofObservation .empty).checked := by
  have member : address.field ∈ plan.targetFields := by simpa using planned
  simp [CheckedRepeatableNumberPlan.read, readAfterNumericDependenciesWith, uncovered, member]

/-- A completed outcome is read at its exact address through the Number dependency cell. -/
theorem repeatableNumberPlan_read_completed (plan : CheckedRepeatableNumberPlan model)
    (input : CheckedDocument model) (completed : List (SourcedNumericTargetOutcome CellAddr))
    (address : CellAddr) (outcome : SourcedNumericTargetOutcome CellAddr)
    (covered : completed.find? (fun outcome => outcome.targetField == address) = some outcome) :
    plan.read input completed address =
      .ok (NumericDependencyCell.ofOutcome outcome.outcome).checked := by
  simp [CheckedRepeatableNumberPlan.read, readAfterNumericDependenciesWith, covered]

end A12Kernel
