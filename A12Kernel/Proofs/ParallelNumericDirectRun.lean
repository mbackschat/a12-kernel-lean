import A12Kernel.Elaboration.ParallelNumericDirectRun
import A12Kernel.Proofs.ParallelComputationClearingPlan

/-! # Direct parallel Number-computation laws -/

namespace A12Kernel

theorem checkedIsolatedParallelNumericDirectRun_wellFormed
    (checked : CheckedIsolatedParallelNumericDirectRun model) :
    checked.WellFormed :=
  ⟨checkedParallelNumericClearingPlan_wellFormed checked.route,
    checked.guardAdmitted, checked.operandScopeAvailable,
    checked.operationScaleAdmitted⟩

end A12Kernel
