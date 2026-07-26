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

end A12Kernel
