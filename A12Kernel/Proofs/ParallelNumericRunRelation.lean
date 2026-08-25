import A12Kernel.Elaboration.ParallelNumericRunRelation
import A12Kernel.Proofs.ComputationRunPlan
import A12Kernel.Proofs.FieldId
import A12Kernel.Proofs.ParallelNumericRun

/-! # Repeatable Number batch-relation laws

The checked plan's unique-target and backward-dependency certificates make successful supplied-order execution a trace of independently enabled whole-table batches. Completed table identity is proved separately from emitted rows so an action-free batch remains a completed dependency.
-/

namespace A12Kernel

private theorem parallelNumericRun_table_ready
    (plan : CheckedParallelNumericPlan model)
    (earlier remaining : List (CheckedParallelNumericAlternativeTable model))
    (table : CheckedParallelNumericAlternativeTable model)
    (split : plan.tables = earlier ++ table :: remaining)
    (state : ParallelNumericTransitionState)
    (stateTargets :
      state.completedTargets = earlier.map (·.targetField)) :
    table.targetField ∉ state.completedTargets ∧
      ParallelNumericDependenciesEnabled plan table state := by
  have unique : (plan.tables.map (·.targetField)).Nodup :=
    checkedParallelNumericPlan_targetFields_nodup plan
  have combined :
      (earlier.map (·.targetField) ++
        table.targetField :: remaining.map (·.targetField)).Nodup := by
    simpa [split, List.map_append] using unique
  have notEarlier : table.targetField ∉ earlier.map (·.targetField) := by
    intro member
    have cross := (List.nodup_append.mp combined).2.2
      table.targetField member table.targetField (by simp)
    exact cross rfl
  constructor
  · simpa [stateTargets] using notEarlier
  · intro dependency dependencyMember referenced
    change dependency ∈ plan.tables.map (·.targetField) at dependencyMember
    have located :
        dependency ∈ earlier.map (·.targetField) ∨
          dependency = table.targetField ∨
            dependency ∈ remaining.map (·.targetField) := by
      simpa [split, List.map_append] using dependencyMember
    rcases located with inEarlier | same | inRemaining
    · rw [stateTargets]
      exact inEarlier
    · subst dependency
      rw [checkedParallelNumericAlternativeTable_excludes_target] at referenced
      contradiction
    · obtain ⟨dependencyTable, dependencyTableMember, rfl⟩ :=
        List.mem_map.mp inRemaining
      have notReferenced := checkedParallelNumericPlan_references_later_false
        plan earlier remaining table dependencyTable split dependencyTableMember
      rw [notReferenced] at referenced
      contradiction

/-- A structural failure transition retains the exact checked table and its
plan-owned target label. -/
theorem parallelNumericRun_failureTransition_identity
    (failure : ParallelNumericRunFailureTransition plan preliminary
      state fault) :
    ∃ table ∈ plan.tables, ∃ error,
      fault = CheckedParallelNumericPlan.ExecutionFault.table
        table.targetField error := by
  cases failure with
  | fail table member pending enabled error executed =>
      exact ⟨table, member, error, rfl⟩

/-- Successful supplied-order suffix execution is admitted by independently enabled whole-table transitions, including batches that emit no addressed outcomes. -/
theorem parallelNumericRun_executeTables_trace
    (plan : CheckedParallelNumericPlan model)
    (preliminary : CheckedIndexPreliminary model)
    (earlier remaining : List (CheckedParallelNumericAlternativeTable model))
    (state : ParallelNumericTransitionState)
    (result : ParallelNumericRunState)
    (split : plan.tables = earlier ++ remaining)
    (stateTargets :
      state.completedTargets = earlier.map (·.targetField))
    (executed :
      plan.executeTables preliminary remaining state.runState = .ok result) :
    ∃ batches final,
      ParallelNumericRunTrace plan preliminary state batches final ∧
        final.completedTargets = plan.targetFields ∧
        final.runState = result := by
  induction remaining generalizing earlier state result with
  | nil =>
      cases executed
      refine ⟨[], state, .nil state, ?_, rfl⟩
      simpa [CheckedParallelNumericPlan.targetFields, split] using stateTargets
  | cons table remaining inductionHypothesis =>
      cases tableResult :
          table.executeWithRead preliminary
            (plan.readPolicy state.runState preliminary.base) with
      | error fault =>
          simp [CheckedParallelNumericPlan.executeTables, tableResult] at executed
      | ok outcomes =>
          simp [CheckedParallelNumericPlan.executeTables, tableResult] at executed
          have ready := parallelNumericRun_table_ready
            plan earlier remaining table split state stateTargets
          let next : ParallelNumericTransitionState := {
            completedTargets := state.completedTargets ++ [table.targetField]
            outcomes := state.outcomes ++ outcomes
          }
          have nextTargets :
              next.completedTargets =
                (earlier ++ [table]).map (·.targetField) := by
            simp [next, List.map_append, stateTargets]
          have nextSplit :
              plan.tables = (earlier ++ [table]) ++ remaining := by
            simpa [List.append_assoc] using split
          obtain ⟨batches, final, trace, finalTargets, finalState⟩ :=
            inductionHypothesis (earlier ++ [table]) next result
              nextSplit nextTargets (by
                simpa [next, ParallelNumericTransitionState.runState]
                  using executed)
          refine ⟨(table.targetField, outcomes) :: batches, final,
            .cons (.compute table ?_ ready.1 ready.2 outcomes tableResult) trace,
            finalTargets, finalState⟩
          rw [split]
          simp

/-- Every successful fixed repeatable Number run has a successful batch trace whose private completion state preserves the exact returned addressed outcomes. -/
theorem parallelNumericRun_execute_trace
    (plan : CheckedParallelNumericPlan model)
    (preliminary : CheckedIndexPreliminary model)
    (outcomes : List ParallelNumericDirectOutcome)
    (executed : plan.execute preliminary = .ok outcomes) :
    ∃ batches final,
      ParallelNumericRunTrace plan preliminary {} batches final ∧
        final.completedTargets = plan.targetFields ∧
        final.outcomes = outcomes := by
  cases runResult : plan.executeTables preliminary plan.tables {} with
  | error fault =>
      simp [CheckedParallelNumericPlan.execute, runResult] at executed
  | ok result =>
      have resultOutcomes : result.completed = outcomes := by
        simpa [CheckedParallelNumericPlan.execute, runResult] using executed
      obtain ⟨batches, final, trace, finalTargets, finalState⟩ :=
        parallelNumericRun_executeTables_trace
          plan preliminary [] plan.tables {} result (by simp) (by simp) runResult
      have finalOutcomes : final.outcomes = outcomes := by
        have stateOutcomes : final.outcomes = result.completed := by
          simpa [ParallelNumericTransitionState.runState] using
            congrArg ParallelNumericRunState.completed finalState
        exact stateOutcomes.trans resultOutcomes
      exact ⟨batches, final, trace, finalTargets, finalOutcomes⟩

/-- A failing supplied-order suffix is exactly a successful whole-table prefix
followed by the enabled table whose structural fault stopped execution. Batch
labels retain action-free table completion separately from flattened addressed
outcomes. -/
theorem parallelNumericRun_executeTables_failureTrace
    (plan : CheckedParallelNumericPlan model)
    (preliminary : CheckedIndexPreliminary model)
    (earlier remaining : List (CheckedParallelNumericAlternativeTable model))
    (state : ParallelNumericTransitionState)
    (fault : CheckedParallelNumericPlan.ExecutionFault)
    (split : plan.tables = earlier ++ remaining)
    (stateTargets :
      state.completedTargets = earlier.map (·.targetField))
    (executed :
      plan.executeTables preliminary remaining state.runState = .error fault) :
    ∃ batches final,
      ParallelNumericRunFailureTrace plan preliminary
        state batches final fault ∧
        state.completedTargets ++ batches.map (·.1) =
          final.completedTargets ∧
        state.outcomes ++ batches.flatMap (·.2) = final.outcomes := by
  induction remaining generalizing earlier state fault with
  | nil =>
      simp only [CheckedParallelNumericPlan.executeTables] at executed
      cases executed
  | cons table remaining inductionHypothesis =>
      cases tableResult :
          table.executeWithRead preliminary
            (plan.readPolicy state.runState preliminary.base) with
      | error error =>
          rw [CheckedParallelNumericPlan.executeTables, tableResult] at executed
          change Except.error (.table table.targetField error) =
            Except.error fault at executed
          cases executed
          have ready := parallelNumericRun_table_ready
            plan earlier remaining table split state stateTargets
          refine ⟨[], state,
            .failed (.fail table ?_ ready.1 ready.2 error tableResult),
            by simp, by simp⟩
          rw [split]
          simp
      | ok outcomes =>
          have remainingExecuted :
              plan.executeTables preliminary remaining
                { completed := state.outcomes ++ outcomes } = .error fault := by
            rw [CheckedParallelNumericPlan.executeTables, tableResult] at executed
            exact executed
          have ready := parallelNumericRun_table_ready
            plan earlier remaining table split state stateTargets
          let next : ParallelNumericTransitionState := {
            completedTargets := state.completedTargets ++ [table.targetField]
            outcomes := state.outcomes ++ outcomes
          }
          have nextTargets :
              next.completedTargets =
                (earlier ++ [table]).map (·.targetField) := by
            simp [next, List.map_append, stateTargets]
          have nextSplit :
              plan.tables = (earlier ++ [table]) ++ remaining := by
            simpa [List.append_assoc] using split
          obtain ⟨batches, final, trace, targetsAppended,
              outcomesAppended⟩ :=
            inductionHypothesis (earlier ++ [table]) next fault
              nextSplit nextTargets (by
                simpa [next, ParallelNumericTransitionState.runState]
                  using remainingExecuted)
          refine ⟨(table.targetField, outcomes) :: batches, final,
            .cons (.compute table ?_ ready.1 ready.2 outcomes tableResult) trace,
            ?_, ?_⟩
          · rw [split]
            simp
          · simpa [next, List.append_assoc] using targetsAppended
          · simpa [next, List.append_assoc] using outcomesAppended

/-- Every failing fixed repeatable Number run has one exact successful batch
prefix and then one enabled target-attributed structural failure. Its final
private state contains exactly the completed table labels and flattened
addressed outcomes of that prefix. -/
theorem parallelNumericRun_execute_failureTrace
    (plan : CheckedParallelNumericPlan model)
    (preliminary : CheckedIndexPreliminary model)
    (fault : CheckedParallelNumericPlan.ExecutionFault)
    (executed : plan.execute preliminary = .error fault) :
    ∃ batches final,
      ParallelNumericRunFailureTrace plan preliminary
        {} batches final fault ∧
        final.completedTargets = batches.map (·.1) ∧
        final.outcomes = batches.flatMap (·.2) := by
  cases runResult : plan.executeTables preliminary plan.tables {} with
  | error cause =>
      rw [CheckedParallelNumericPlan.execute, runResult] at executed
      change Except.error cause = Except.error fault at executed
      cases executed
      obtain ⟨batches, final, trace, targetsAppended,
          outcomesAppended⟩ :=
        parallelNumericRun_executeTables_failureTrace
          plan preliminary [] plan.tables {} fault (by simp) (by simp)
            runResult
      exact ⟨batches, final, trace, by simpa using targetsAppended.symm,
        by simpa using outcomesAppended.symm⟩
  | ok state =>
      rw [CheckedParallelNumericPlan.execute, runResult] at executed
      change Except.ok state.completed = Except.error fault at executed
      cases executed

end A12Kernel
