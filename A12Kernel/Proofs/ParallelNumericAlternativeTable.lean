import A12Kernel.Elaboration.ParallelNumericAlternativeTable
import A12Kernel.Proofs.ParallelNumericDirectRun

/-! # Parallel Number alternative-table laws -/

namespace A12Kernel

theorem checkedParallelNumericAlternativeTable_wellFormed
    (table : CheckedParallelNumericAlternativeTable model) :
    table.WellFormed := by
  intro alternative member
  exact ⟨checkedIsolatedParallelNumericDirectRun_wellFormed
      alternative.operation,
    alternative.preconditionOwned, alternative.targetMatches⟩

/-- No checked row's guard bans, or expression reads, the table target. -/
theorem checkedParallelNumericAlternativeTable_excludes_target
    (table : CheckedParallelNumericAlternativeTable model) :
    table.forbidsField table.targetField = false := by
  unfold CheckedParallelNumericAlternativeTable.forbidsField
  apply List.any_eq_false.mpr
  intro alternative member
  have excluded :=
    checkedIsolatedParallelNumericDirectRun_excludes_target
      alternative.operation
  simpa [alternative.targetMatches] using excluded

theorem parallelNumericAlternativeTable_noMatch
    (table : CheckedParallelNumericAlternativeTable model)
    (context : ParallelNumericGuardContext)
    (selection : ComputationAlternative.selectFirstWith (fun guard => guard.eval context)
      table.selectableAlternatives = .ok .noMatch) :
    table.evaluate context = .ok .noValue := by
  simp [CheckedParallelNumericAlternativeTable.evaluate, selection]

theorem parallelNumericAlternativeTable_guardPoison
    (table : CheckedParallelNumericAlternativeTable model)
    (context : ParallelNumericGuardContext) (cause : FormalCause)
    (selection : ComputationAlternative.selectFirstWith (fun guard => guard.eval context)
      table.selectableAlternatives = .ok (.poison cause)) :
    table.evaluate context = .ok (.inheritedPoison cause) := by
  simp [CheckedParallelNumericAlternativeTable.evaluate, selection]

theorem parallelNumericAlternativeTable_selected
    (table : CheckedParallelNumericAlternativeTable model)
    (context : ParallelNumericGuardContext)
    (operation : CheckedIsolatedParallelNumericDirectRun model)
    (selection : ComputationAlternative.selectFirstWith (fun guard => guard.eval context)
      table.selectableAlternatives = .ok (.selected operation)) :
    table.evaluate context = operation.evaluateSelected context := by
  simp [CheckedParallelNumericAlternativeTable.evaluate, selection]

private theorem parallelNumericAlternativeTable_executeTargetWith_address
    (table : CheckedParallelNumericAlternativeTable model)
    (preliminary : CheckedIndexPreliminary model)
    (read : CellAddr → Except CheckedDocumentError CheckedCell)
    (ordinaryAt : Env → NumericComputationEvaluationContext)
    (target : ParallelNumericTargetCoverage)
    (outcome : ParallelNumericDirectOutcome)
    (executed :
      table.executeTargetWith preliminary read ordinaryAt target = .ok outcome) :
    outcome.address = target.address := by
  unfold CheckedParallelNumericAlternativeTable.executeTargetWith at executed
  cases keyResult :
      table.first.operation.targetKeyFor preliminary
        target.environment target.address with
  | error error =>
      simp [keyResult, Bind.bind, Except.bind] at executed
  | ok key =>
      cases cellsResult :
          table.operandCellsWith preliminary read
            target.environment key with
      | error error =>
          simp [keyResult, cellsResult, Bind.bind, Except.bind] at executed
      | ok cells =>
          cases partnersResult :
              CheckedIsolatedParallelNumericDirectRun.partnerEnvironments (table.operandRoutes.map (·.join))
                preliminary target.environment key with
          | error error =>
              simp [keyResult, cellsResult, partnersResult, Bind.bind, Except.bind] at executed
          | ok partners =>
              rw [keyResult] at executed
              simp only [Bind.bind, Except.bind] at executed
              rw [cellsResult] at executed
              simp only at executed
              rw [partnersResult] at executed
              let context := CheckedIsolatedParallelNumericDirectRun.guardContextAt cells partners
                ordinaryAt target.environment
              change
                (do
                  let result ← table.evaluate context
                  pure ({
                    address := target.address
                    outcome := result
                  } : ParallelNumericDirectOutcome)) =
                    .ok outcome at executed
              cases evaluationResult :
                  table.evaluate context with
              | error error =>
                  rw [evaluationResult] at executed
                  contradiction
              | ok result =>
                  rw [evaluationResult] at executed
                  change Except.ok _ = Except.ok outcome at executed
                  cases executed
                  rfl

/-- Successful table execution emits exact addresses only for the table's checked target field. -/
theorem parallelNumericAlternativeTable_executeWithRead_owns_target
    (table : CheckedParallelNumericAlternativeTable model)
    (preliminary : CheckedIndexPreliminary model)
    (read : CellAddr → Except CheckedDocumentError CheckedCell)
    (ordinaryAt : Env → NumericComputationEvaluationContext)
    (outcomes : List ParallelNumericDirectOutcome)
    (executed :
      table.executeWithRead preliminary read ordinaryAt = .ok outcomes) :
    ∀ outcome ∈ outcomes,
      outcome.address.field = table.targetField := by
  unfold CheckedParallelNumericAlternativeTable.executeWithRead at executed
  cases targetsResult :
      CheckedIsolatedParallelNumericDirectRun.executableTargets
        table.first.operation.route.join
        ((table.operandRoutes.drop 1).map (·.join)) preliminary with
  | error error =>
      rw [targetsResult] at executed
      contradiction
  | ok targets =>
      rw [targetsResult] at executed
      have targetsOwned :
          ∀ target ∈ targets,
            target.address.field = table.targetField := by
        intro target member
        have owned :=
          parallelNumericExecutableTargets_own_primary_target
            table.first.operation.route.join
            ((table.operandRoutes.drop 1).map (·.join)) preliminary targets
            targetsResult target member
        change
          target.address.field =
            table.first.operation.route.targetField at owned
        exact owned.trans table.first.targetMatches
      change
        targets.mapM (table.executeTargetWith preliminary read ordinaryAt) =
          .ok outcomes at executed
      apply exceptMapM_all_of_step
        (property := fun outcome =>
          outcome.address.field = table.targetField)
        (mapped := executed)
      intro target member outcome targetExecuted
      rw [parallelNumericAlternativeTable_executeTargetWith_address
        table preliminary read ordinaryAt target outcome targetExecuted]
      exact targetsOwned target member

/-- Successful table execution emits each exact target address at most once. -/
theorem parallelNumericAlternativeTable_executeWithRead_addresses_nodup
    (table : CheckedParallelNumericAlternativeTable model)
    (preliminary : CheckedIndexPreliminary model)
    (read : CellAddr → Except CheckedDocumentError CheckedCell)
    (ordinaryAt : Env → NumericComputationEvaluationContext)
    (outcomes : List ParallelNumericDirectOutcome)
    (executed :
      table.executeWithRead preliminary read ordinaryAt = .ok outcomes) :
    (outcomes.map (·.address)).Nodup := by
  unfold CheckedParallelNumericAlternativeTable.executeWithRead at executed
  cases targetsResult :
      CheckedIsolatedParallelNumericDirectRun.executableTargets
        table.first.operation.route.join
        ((table.operandRoutes.drop 1).map (·.join)) preliminary with
  | error error =>
      rw [targetsResult] at executed
      contradiction
  | ok targets =>
      rw [targetsResult] at executed
      change
        targets.mapM (table.executeTargetWith preliminary read ordinaryAt) =
          .ok outcomes at executed
      have projected := exceptMapM_map_eq_of_step
        (table.executeTargetWith preliminary read ordinaryAt)
        (·.address) (·.address) targets outcomes
        (by
          intro target member outcome targetExecuted
          exact
            parallelNumericAlternativeTable_executeTargetWith_address
              table preliminary read ordinaryAt target outcome targetExecuted)
        executed
      rw [projected]
      exact parallelNumericExecutableTargets_addresses_nodup
        table.first.operation.route.join
        ((table.operandRoutes.drop 1).map (·.join)) preliminary targets targetsResult

end A12Kernel
