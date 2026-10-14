import A12Kernel.Elaboration.ParallelNumericStep
import A12Kernel.Proofs.ParallelNumericDirectRun

/-! # Target exclusion across parallel step forms -/
namespace A12Kernel

/-- Every joined operation retains its guard target ban and expression self-reference exclusion
after table assembly. Ordinary members retain their own target-ban certificates and containing-group
exemptions. -/
theorem parallelNumericStep_operations_exclude_target
    (step : CheckedParallelNumericStep model) :
    ∀ operation ∈ step.operations, operation.forbidsField step.targetField = false := by
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
      change alternative.operation.forbidsField table.targetField = false
      simpa only [alternative.targetMatches] using
        checkedIsolatedParallelNumericDirectRun_excludes_target alternative.operation
  | mixed table =>
      intro operation member
      change operation ∈ table.members.filterMap CheckedParallelNumericMember.joinedOperation? at member
      obtain ⟨entry, _, selected⟩ := List.mem_filterMap.mp member
      cases entry with
      | bound policy alternative => simp [CheckedParallelNumericMember.joinedOperation?] at selected
      | joined alternative =>
          have same : alternative.operation = operation := Option.some.inj selected
          subst operation
          change alternative.operation.forbidsField table.targetField = false
          simpa only [alternative.targetMatches] using
            checkedIsolatedParallelNumericDirectRun_excludes_target alternative.operation

end A12Kernel
