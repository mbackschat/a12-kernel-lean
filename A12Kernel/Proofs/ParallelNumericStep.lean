import A12Kernel.Elaboration.ParallelNumericStep
import A12Kernel.Proofs.ParallelNumericDirectRun

/-! # Target exclusion across parallel step forms -/
namespace A12Kernel

/-- Scheduling a singleton or a guarded table preserves every operation's full guard/expression
self-reference exclusion; packing alternatives cannot change which target that certificate names. -/
theorem parallelNumericStep_operations_exclude_target
    (step : CheckedParallelNumericStep model) :
    ∀ operation ∈ step.operations, operation.referencesField step.targetField = false := by
  cases step with
  | single checked =>
      intro operation member
      change operation ∈ [checked] at member
      have same := List.mem_singleton.mp member
      subst operation
      exact checkedIsolatedParallelNumericDirectRun_excludes_target checked
  | alternatives table =>
      intro operation member
      change operation ∈ table.alternatives.map (·.operation) at member
      obtain ⟨alternative, _, rfl⟩ := List.mem_map.mp member
      change alternative.operation.referencesField table.targetField = false
      simpa only [alternative.targetMatches] using
        checkedIsolatedParallelNumericDirectRun_excludes_target alternative.operation

end A12Kernel
