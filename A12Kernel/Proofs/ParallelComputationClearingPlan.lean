import A12Kernel.Elaboration.ParallelComputationClearing
import A12Kernel.Proofs.CheckedIndexColumn

/-! # Checked parallel-computation clearing-plan laws -/

namespace A12Kernel

theorem checkedParallelNumericClearingPlan_wellFormed
    (plan : CheckedParallelNumericClearingPlan model) :
    plan.WellFormed :=
  ⟨checkedParallelIndexGroups_wellFormed plan.groups,
    plan.targetResolved, plan.operandResolved, plan.targetNumber,
    plan.operandNumber, plan.targetPolicyOwned, plan.targetGroup,
    plan.operandGroup, plan.targetScope, plan.operandScope⟩

/-- Target-instance enumeration depends on checked physical row topology, never on placed target-cell payloads. -/
theorem parallelNumericTargetEnvironments_cells_irrelevant
    (plan : CheckedParallelNumericClearingPlan model)
    (left right : CheckedDocument model)
    (rows :
      left.source.instantiatedRows =
        right.source.instantiatedRows) :
    plan.targetEnvironments left =
      plan.targetEnvironments right := by
  simp [CheckedParallelNumericClearingPlan.targetEnvironments,
    CheckedDocument.actualRowEnvironments, rows]

@[simp] theorem parallelNumericClearingMark_targetScope
    (plan : CheckedParallelNumericClearingPlan model)
    (side : ParallelComputationIndexSide) :
    (plan.markPlanFor side).targetScope =
      plan.targetDeclaration.repeatableScope := by
  cases side <;> rfl

end A12Kernel
