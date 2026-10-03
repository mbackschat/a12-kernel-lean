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
  unfold CheckedIsolatedParallelNumericDirectRun.executableTargets
    CheckedIsolatedParallelNumericDirectRun.targetCoverage at executed
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
        rename_i _ coverage covered
        split at covered
        · contradiction
        · change Except.ok _ = Except.ok coverage at covered
          cases covered
          intro target member
          obtain ⟨original, primaryMember, rfl⟩ :=
            List.mem_map.mp (List.mem_filter.mp member).1
          exact parallelNumericTargetRoute_coverage_owns_target
            primary preliminary primaryCoverage primaryResult original primaryMember

/-- Executable-target filtering preserves exact address uniqueness from primary coverage. -/
theorem parallelNumericExecutableTargets_addresses_nodup
    (primary : CheckedParallelNumericTargetRoute model)
    (additional : List (CheckedParallelNumericTargetRoute model))
    (preliminary : CheckedIndexPreliminary model)
    (targets : List ParallelNumericTargetCoverage)
    (executed :
      CheckedIsolatedParallelNumericDirectRun.executableTargets
        primary additional preliminary = .ok targets) :
    (targets.map (·.address)).Nodup := by
  unfold CheckedIsolatedParallelNumericDirectRun.executableTargets
    CheckedIsolatedParallelNumericDirectRun.targetCoverage at executed
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
        rename_i _ coverage covered
        split at covered
        · contradiction
        · change Except.ok _ = Except.ok coverage at covered
          cases covered
          apply (List.filter_sublist.map (fun target : ParallelNumericTargetCoverage => target.address)).nodup
          simpa [List.map_map, Function.comp_def] using parallelNumericTargetRoute_coverage_addresses_nodup
            primary preliminary primaryCoverage primaryResult

end A12Kernel
