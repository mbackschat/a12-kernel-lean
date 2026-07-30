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

theorem parallelNumericAlternativeTable_noMatch
    (table : CheckedParallelNumericAlternativeTable model)
    (context : ScalarComputationContext)
    (selection : ComputationAlternative.selectFirst
      table.selectableAlternatives context = .noMatch) :
    table.evaluate context = .ok .noValue := by
  simp [CheckedParallelNumericAlternativeTable.evaluate, selection]

theorem parallelNumericAlternativeTable_guardPoison
    (table : CheckedParallelNumericAlternativeTable model)
    (context : ScalarComputationContext) (cause : FormalCause)
    (selection : ComputationAlternative.selectFirst
      table.selectableAlternatives context = .poison cause) :
    table.evaluate context = .ok (.inheritedPoison cause) := by
  simp [CheckedParallelNumericAlternativeTable.evaluate, selection]

theorem parallelNumericAlternativeTable_selected
    (table : CheckedParallelNumericAlternativeTable model)
    (context : ScalarComputationContext)
    (operation : CheckedIsolatedParallelNumericDirectRun model)
    (selection : ComputationAlternative.selectFirst
      table.selectableAlternatives context = .selected operation) :
    table.evaluate context = operation.evaluateSelected context := by
  simp [CheckedParallelNumericAlternativeTable.evaluate, selection]

/-- Successful table execution emits exact addresses only for the table's checked target field. -/
theorem parallelNumericAlternativeTable_executeWithRead_owns_target
    (table : CheckedParallelNumericAlternativeTable model)
    (preliminary : CheckedIndexPreliminary model)
    (read : CellAddr → Except CheckedDocumentError CheckedCell)
    (outcomes : List ParallelNumericDirectOutcome)
    (executed :
      table.executeWithRead preliminary read = .ok outcomes) :
    ∀ outcome ∈ outcomes,
      outcome.address.field = table.targetField := by
  unfold CheckedParallelNumericAlternativeTable.executeWithRead at executed
  cases targetsResult :
      CheckedIsolatedParallelNumericDirectRun.executableTargets
        table.first.operation.route.asTargetRoute
        (table.operandRoutes.drop 1) preliminary with
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
            table.first.operation.route.asTargetRoute
            (table.operandRoutes.drop 1) preliminary targets
            targetsResult target member
        change
          target.address.field =
            table.first.operation.route.targetField at owned
        exact owned.trans table.first.targetMatches
      change
        targets.mapM (table.executeTargetWith preliminary read) =
          .ok outcomes at executed
      apply exceptMapM_all_of_step
        (property := fun outcome =>
          outcome.address.field = table.targetField)
        (mapped := executed)
      intro target member outcome targetExecuted
      unfold CheckedParallelNumericAlternativeTable.executeTargetWith
        at targetExecuted
      cases keyResult :
          table.first.operation.targetKeyFor preliminary
            target.environment target.address with
      | error error =>
          simp [keyResult, Bind.bind, Except.bind] at targetExecuted
      | ok key =>
          cases cellsResult :
              table.operandCellsWith preliminary read
                target.environment key with
          | error error =>
              simp [keyResult, cellsResult, Bind.bind, Except.bind]
                at targetExecuted
          | ok cells =>
              rw [keyResult] at targetExecuted
              simp only [Bind.bind, Except.bind] at targetExecuted
              rw [cellsResult] at targetExecuted
              let context : ScalarComputationContext := {
                read := fun field =>
                  match cells.find? fun cell => cell.1 == field with
                  | some cell => cell.2
                  | none => malformedCheckedCell
              }
              change
                (do
                  let result ← table.evaluate context
                  pure ({
                    address := target.address
                    outcome := result
                  } : ParallelNumericDirectOutcome)) =
                    .ok outcome at targetExecuted
              cases evaluationResult : table.evaluate context with
              | error error =>
                  rw [evaluationResult] at targetExecuted
                  contradiction
              | ok result =>
                  rw [evaluationResult] at targetExecuted
                  change Except.ok _ = Except.ok outcome at targetExecuted
                  cases targetExecuted
                  exact targetsOwned target member

end A12Kernel
