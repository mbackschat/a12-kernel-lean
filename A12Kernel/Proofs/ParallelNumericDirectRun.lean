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
    checked.routeTargetsCoherent, checked.guardExcludesTarget,
    checked.expressionExcludesTarget, checked.guardAdmitted,
    checked.expressionUsesOperand, checked.expressionOperandsAdmitted,
    checked.expressionAdmitted, checked.expressionAuthoring,
    checked.operandScopesAvailable,
    checked.operationScaleOwned, checked.operationScaleAdmitted⟩

/-- A checked repeatable Number operation cannot read its own target through either its guard or expression. -/
theorem checkedIsolatedParallelNumericDirectRun_excludes_target
    (checked : CheckedIsolatedParallelNumericDirectRun model) :
    checked.referencesField checked.route.targetField = false := by
  simp [CheckedIsolatedParallelNumericDirectRun.referencesField,
    checked.guardExcludesTarget, checked.expressionExcludesTarget]

/-- Executable-target filtering preserves the primary route's target field. -/
theorem parallelNumericExecutableTargets_own_primary_target
    (primary : CheckedParallelNumericTargetRoute model)
    (additional : List (CheckedParallelNumericTargetRoute model))
    (preliminary : CheckedIndexPreliminary model)
    (targets : List ParallelNumericTargetCoverage)
    (executed :
      CheckedIsolatedParallelNumericDirectRun.executableTargets
        primary additional preliminary = .ok targets) :
    ∀ target ∈ targets,
      target.address.field = primary.targetField := by
  unfold CheckedIsolatedParallelNumericDirectRun.executableTargets at executed
  cases primaryResult : primary.targetCoverage preliminary with
  | error error =>
      simp [primaryResult, Except.mapError, Bind.bind, Except.bind]
        at executed
  | ok primaryCoverage =>
      simp [primaryResult, Except.mapError, Bind.bind, Except.bind]
        at executed
      split at executed
      · contradiction
      · change Except.ok _ = Except.ok targets at executed
        cases executed
        intro target member
        have primaryMember :
            target ∈ primaryCoverage :=
          (List.mem_filter.mp member).1
        exact parallelNumericTargetRoute_coverage_owns_target
          primary preliminary primaryCoverage primaryResult
          target primaryMember

end A12Kernel
