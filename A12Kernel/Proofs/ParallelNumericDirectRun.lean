import A12Kernel.Elaboration.ParallelNumericDirectRun
import A12Kernel.Proofs.ParallelComputationClearingPlan

/-! # Direct parallel Number-computation laws -/

namespace A12Kernel

theorem checkedIsolatedParallelNumericDirectRun_wellFormed
    (checked : CheckedIsolatedParallelNumericDirectRun model) :
    checked.WellFormed :=
  ⟨checkedParallelNumericClearingPlan_wellFormed checked.route,
    fun additional _ =>
      checkedParallelNumericTargetRoute_wellFormed additional,
    checked.routeTargetsCoherent, checked.guardAdmitted,
    checked.expressionUsesOperand, checked.expressionOperandsAdmitted,
    checked.expressionAdmitted, checked.expressionAuthoring,
    checked.operandScopesAvailable,
    checked.operationScaleOwned, checked.operationScaleAdmitted⟩

end A12Kernel
