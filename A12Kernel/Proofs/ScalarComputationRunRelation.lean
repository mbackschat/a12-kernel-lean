import A12Kernel.Elaboration.ScalarComputationRunRelation
import A12Kernel.Proofs.ComputationRunPlan
import A12Kernel.Proofs.FieldId
import A12Kernel.Proofs.NumericComputationRunRelation
import A12Kernel.Proofs.ScalarComputationRun
import A12Kernel.Proofs.StringComputationRunRelation

/-! # Mixed scalar run relation laws

The checked mixed plan's unique-target and backward-dependency certificates make its successful fixed execution a trace of independently enabled String and Number transitions.
-/

namespace A12Kernel

private theorem checkedStringComputationTable_evaluateCompletion_target
    (table : CheckedStringComputationTable model)
    (patterns : PreparedFlatStringPatterns model compilePattern)
    (context : StringComputationContext)
    (completion : StringComputationRunCompletion)
    (evaluated :
      table.evaluateCompletion patterns context = .ok completion) :
    completion.targetField = table.targetField := by
  cases matcher : patterns.targetMatcher? table.targetField with
  | none =>
      simp [CheckedStringComputationTable.evaluateCompletion, matcher] at evaluated
  | some targetMatcher =>
      cases outcome : table.evaluateOutcomeWithPattern targetMatcher context with
      | error fault =>
          simp [CheckedStringComputationTable.evaluateCompletion,
            matcher, outcome] at evaluated
      | ok result =>
          cases dependency : StringDependencyCell.ofOutcome result with
          | error fault =>
              simp [CheckedStringComputationTable.evaluateCompletion,
                matcher, outcome, dependency] at evaluated
          | ok cell =>
              simp [CheckedStringComputationTable.evaluateCompletion,
                matcher, outcome, dependency] at evaluated
              cases evaluated
              rfl

private theorem checkedNumericComputationTable_evaluateCompletion_target
    (table : CheckedNumericComputationTable model)
    (context : ScalarComputationContext)
    (completion : NumericComputationRunCompletion)
    (evaluated : table.evaluateCompletion context = .ok completion) :
    completion.targetField = table.targetField := by
  cases result : table.evaluate context with
  | error fault =>
      simp [CheckedNumericComputationTable.evaluateCompletion, result] at evaluated
  | ok checked =>
      cases checked with
      | unsupported fault =>
          simp [CheckedNumericComputationTable.evaluateCompletion, result] at evaluated
      | supported outcome =>
          simp [CheckedNumericComputationTable.evaluateCompletion, result] at evaluated
          cases evaluated
          rfl

/-- Successful mixed atomic evaluation retains the selected step's target. -/
theorem scalarComputationRun_evaluateStep_target
    (run : CheckedScalarComputationRun model)
    (world : World)
    (patterns : PreparedFlatStringPatterns model compilePattern)
    (input : CheckedDocument model)
    (state : ScalarComputationRunState)
    (step : CheckedScalarComputationStep model)
    (completion : ScalarComputationCompletion)
    (evaluated :
      run.evaluateStep world patterns input state step = .ok completion) :
    completion.targetField = step.targetField := by
  cases step with
  | string table =>
      cases result : table.evaluateCompletion patterns
          (run.stringContext state input) with
      | error fault =>
          simp [CheckedScalarComputationRun.evaluateStep, result] at evaluated
      | ok stringCompletion =>
          simp [CheckedScalarComputationRun.evaluateStep, result] at evaluated
          cases evaluated
          exact checkedStringComputationTable_evaluateCompletion_target
            table patterns (run.stringContext state input) stringCompletion result
  | number table =>
      cases result : table.evaluateCompletion
          (run.numberContext world state input) with
      | error fault =>
          simp [CheckedScalarComputationRun.evaluateStep, result] at evaluated
      | ok numberCompletion =>
          simp [CheckedScalarComputationRun.evaluateStep, result] at evaluated
          cases evaluated
          exact checkedNumericComputationTable_evaluateCompletion_target
            table (run.numberContext world state input) numberCompletion result

private theorem checkedScalarComputationStep_excludes_target
    (step : CheckedScalarComputationStep model) :
    step.referencesField step.targetField = false := by
  cases step with
  | string table => exact checkedStringComputationTable_excludes_target table
  | number table => exact checkedNumericComputationTable_excludes_target table

private theorem scalarComputationRun_step_ready
    (run : CheckedScalarComputationRun model)
    (earlier remaining : List (CheckedScalarComputationStep model))
    (step : CheckedScalarComputationStep model)
    (split : run.steps = earlier ++ step :: remaining)
    (state : ScalarComputationRunState)
    (stateTargets : state.targetFields = earlier.map (·.targetField)) :
    step.targetField ∉ state.targetFields ∧
      ScalarComputationDependenciesEnabled run step state := by
  have unique : (run.steps.map (·.targetField)).Nodup :=
    (fieldId_firstDuplicate_none_iff_nodup _).mp run.uniqueTargets
  have combined :
      (earlier.map (·.targetField) ++
        step.targetField :: remaining.map (·.targetField)).Nodup := by
    simpa [split, List.map_append] using unique
  have notEarlier : step.targetField ∉ earlier.map (·.targetField) := by
    intro member
    have cross := (List.nodup_append.mp combined).2.2
      step.targetField member step.targetField (by simp)
    exact cross rfl
  constructor
  · simpa [stateTargets] using notEarlier
  · intro dependency dependencyMember referenced
    change dependency ∈ run.steps.map (·.targetField) at dependencyMember
    have located :
        dependency ∈ earlier.map (·.targetField) ∨
          dependency = step.targetField ∨
            dependency ∈ remaining.map (·.targetField) := by
      simpa [split, List.map_append] using dependencyMember
    rcases located with inEarlier | same | inRemaining
    · rw [stateTargets]
      exact inEarlier
    · subst dependency
      rw [checkedScalarComputationStep_excludes_target] at referenced
      contradiction
    · obtain ⟨dependencyStep, dependencyStepMember, rfl⟩ :=
        List.mem_map.mp inRemaining
      have orderedSuffix :
          firstForwardScalarComputationDependency? (step :: remaining) = none :=
        firstForwardComputationDependency_none_suffix
          CheckedScalarComputationStep.targetField
          CheckedScalarComputationStep.referencesField
          earlier (step :: remaining) (by
            simpa [firstForwardScalarComputationDependency?, split]
              using run.dependenciesOrdered)
      have notReferenced :=
        firstForwardComputationDependency_none_head
          CheckedScalarComputationStep.targetField
          CheckedScalarComputationStep.referencesField
          step remaining orderedSuffix dependencyStep dependencyStepMember
      rw [notReferenced] at referenced
      contradiction

/-- Successful fixed-order suffix execution is admitted by the mixed transition relation and carries exactly the newly appended rich outcomes. -/
theorem scalarComputationRun_executeSteps_trace
    (run : CheckedScalarComputationRun model)
    (world : World)
    (patterns : PreparedFlatStringPatterns model compilePattern)
    (input : CheckedDocument model)
    (earlier remaining : List (CheckedScalarComputationStep model))
    (state result : ScalarComputationRunState)
    (split : run.steps = earlier ++ remaining)
    (stateTargets : state.targetFields = earlier.map (·.targetField))
    (executed :
      run.executeSteps world patterns input remaining state = .ok result) :
    ∃ outcomes,
      ScalarComputationRunTrace run world patterns input state outcomes result ∧
        state.outcomes ++ outcomes = result.outcomes := by
  induction remaining generalizing earlier state result with
  | nil =>
      cases executed
      exact ⟨[], .nil state, by simp⟩
  | cons step remaining inductionHypothesis =>
      cases evaluated : run.evaluateStep world patterns input state step with
      | error fault =>
          simp [CheckedScalarComputationRun.executeSteps, evaluated,
            Bind.bind, Except.bind] at executed
      | ok completion =>
          simp [CheckedScalarComputationRun.executeSteps, evaluated] at executed
          have target := scalarComputationRun_evaluateStep_target
            run world patterns input state step completion evaluated
          have ready := scalarComputationRun_step_ready
            run earlier remaining step split state stateTargets
          let next : ScalarComputationRunState :=
            { completed := state.completed ++ [completion] }
          have nextTargets :
              next.targetFields =
                (earlier ++ [step]).map (·.targetField) := by
            have stateTargets' :
                state.completed.map (·.targetField) =
                  earlier.map (·.targetField) := by
              simpa [ScalarComputationRunState.targetFields] using stateTargets
            simp [next, ScalarComputationRunState.targetFields,
              List.map_append, stateTargets', target]
          have nextSplit :
              run.steps = (earlier ++ [step]) ++ remaining := by
            simpa [List.append_assoc] using split
          obtain ⟨outcomes, trace, appended⟩ :=
            inductionHypothesis (earlier ++ [step]) next result
              nextSplit nextTargets executed
          refine ⟨completion.outcome :: outcomes,
            .cons (.compute step ?_ ready.1 ready.2 completion evaluated) trace,
            ?_⟩
          · rw [split]
            simp
          · simpa [next, ScalarComputationRunState.outcomes,
              List.append_assoc] using appended

/-- Every successful fixed mixed execution has a non-self-justifying transition trace with exactly its returned outcomes. -/
theorem scalarComputationRun_execute_trace
    (run : CheckedScalarComputationRun model)
    (world : World)
    (patterns : PreparedFlatStringPatterns model compilePattern)
    (input : CheckedDocument model)
    (outcomes : List ScalarComputationOutcome)
    (executed : run.execute world patterns input = .ok outcomes) :
    ∃ result,
      ScalarComputationRunTrace run world patterns input {} outcomes result ∧
        result.outcomes = outcomes := by
  cases runResult : run.executeSteps world patterns input run.steps {} with
  | error fault =>
      simp [CheckedScalarComputationRun.execute, runResult,
        Functor.map, Except.map] at executed
  | ok result =>
      have resultOutcomes : result.outcomes = outcomes := by
        simpa [CheckedScalarComputationRun.execute, runResult,
          Functor.map, Except.map] using executed
      obtain ⟨labels, trace, labelsEqual⟩ :=
        scalarComputationRun_executeSteps_trace
          run world patterns input [] run.steps {} result (by simp)
            (by simp [ScalarComputationRunState.targetFields]) runResult
      have labelsResult : labels = result.outcomes := by
        simpa [ScalarComputationRunState.outcomes] using labelsEqual
      rw [labelsResult, resultOutcomes] at trace
      exact ⟨result, trace, resultOutcomes⟩

end A12Kernel
