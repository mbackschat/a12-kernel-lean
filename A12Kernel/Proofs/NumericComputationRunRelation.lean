import A12Kernel.Elaboration.NumericComputation.RunRelation
import A12Kernel.Proofs.NumericComputationRun

/-! # Checked Number-run relation laws -/

namespace A12Kernel

/-- Every successful step label names a target owned by the checked run. -/
theorem numericComputationRunStep_target_mem
    (step : NumericComputationRunStep run input state label next) :
    label.1 ∈ run.targetFields := by
  cases step with
  | compute table member pending enabled completion evaluated =>
      rw [numericComputationRun_evaluateTable_target
        run input state table completion evaluated]
      exact List.mem_map.mpr ⟨table, member, rfl⟩

end A12Kernel
