import A12Kernel.Elaboration.StringComputationRunRelation
import A12Kernel.Proofs.ComputationRunPlan
import A12Kernel.Proofs.StringComputationRun
import A12Kernel.Proofs.FieldId

/-! # Checked String-run relation laws

The proof spine derives fixed-order trace soundness from the checked plan's two static certificates rather than defining the relation as executor equality.
-/

namespace A12Kernel

theorem checkedStringComputationTable_excludes_target
    (table : CheckedStringComputationTable model) :
    table.referencesField table.targetField = false := by
  simp only [CheckedStringComputationTable.referencesField,
    CheckedStringComputationAlternative.referencesField,
    List.any_eq_false]
  intro alternative member
  have guardExcludes :
      alternative.precondition.any
        (·.referencesField table.targetField) = false := by
    cases guard : alternative.precondition with
    | none => rfl
    | some condition =>
        simpa [guard] using alternative.guardExcludesTarget
  simp [guardExcludes, alternative.expressionExcludesTarget]

/-- Successful atomic evaluation cannot substitute another target into a completion. -/
theorem stringComputationRun_evaluateTable_target
    (run : CheckedStringComputationRun model)
    (patterns : PreparedFlatStringPatterns model compilePattern)
    (input : CheckedDocument model) (state : StringComputationRunState)
    (table : CheckedStringComputationTable model)
    (completion : StringComputationRunCompletion)
    (evaluated : run.evaluateTable patterns input state table = .ok completion) :
    completion.targetField = table.targetField := by
  cases matcher : patterns.targetMatcher? table.targetField with
  | none =>
      simp [CheckedStringComputationRun.evaluateTable,
        CheckedStringComputationTable.evaluateCompletion, matcher] at evaluated
  | some targetMatcher =>
      cases outcome :
          table.evaluateOutcomeWithPattern targetMatcher
            (run.readPolicy state input) with
      | error fault =>
          simp [CheckedStringComputationRun.evaluateTable,
            CheckedStringComputationTable.evaluateCompletion,
            matcher, outcome] at evaluated
      | ok result =>
          cases dependency : StringDependencyCell.ofOutcome result with
          | error fault =>
              simp [CheckedStringComputationRun.evaluateTable,
                CheckedStringComputationTable.evaluateCompletion,
                matcher, outcome, dependency] at evaluated
          | ok cell =>
              simp [CheckedStringComputationRun.evaluateTable,
                CheckedStringComputationTable.evaluateCompletion,
                matcher, outcome, dependency] at evaluated
              cases evaluated
              rfl

private theorem stringComputationRun_table_ready
    (run : CheckedStringComputationRun model)
    (earlier remaining : List (CheckedStringComputationTable model))
    (table : CheckedStringComputationTable model)
    (split : run.tables = earlier ++ table :: remaining)
    (state : StringComputationRunState)
    (stateTargets :
      state.targetFields = earlier.map (·.targetField)) :
    table.targetField ∉ state.targetFields ∧
      StringComputationDependenciesEnabled run table state := by
  have unique : (run.tables.map (·.targetField)).Nodup :=
    (fieldId_firstDuplicate_none_iff_nodup _).mp run.uniqueTargets
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
    rw [split] at dependencyMember
    simp only [List.mem_append, List.mem_cons] at dependencyMember
    rcases dependencyMember with inEarlier | same | inRemaining
    · rw [stateTargets]
      exact List.mem_map.mpr ⟨dependency, inEarlier, rfl⟩
    · subst dependency
      rw [checkedStringComputationTable_excludes_target] at referenced
      contradiction
    · have orderedSuffix :
          firstForwardStringDependency? (table :: remaining) = none :=
        by
          have generic :=
            firstForwardComputationDependency_none_suffix
              (fun candidate : CheckedStringComputationTable model =>
                candidate.targetField)
              (fun candidate field =>
                candidate.referencesField field)
              earlier (table :: remaining) (by
                simpa [firstForwardStringDependency?, split]
                  using run.dependenciesOrdered)
          simpa [firstForwardStringDependency?] using generic
      have notReferenced :=
        firstForwardComputationDependency_none_head
          (fun candidate : CheckedStringComputationTable model =>
            candidate.targetField)
          (fun candidate field => candidate.referencesField field)
          table remaining (by
            simpa [firstForwardStringDependency?] using orderedSuffix)
          dependency inRemaining
      rw [notReferenced] at referenced
      contradiction

/-- Successful fixed-order suffix execution is admitted by the independent relation and carries exactly the newly appended rich outcomes as labels. -/
theorem stringComputationRun_executeTables_trace
    (run : CheckedStringComputationRun model)
    (patterns : PreparedFlatStringPatterns model compilePattern)
    (input : CheckedDocument model)
    (earlier remaining : List (CheckedStringComputationTable model))
    (state result : StringComputationRunState)
    (split : run.tables = earlier ++ remaining)
    (stateTargets : state.targetFields = earlier.map (·.targetField))
    (executed : run.executeTables patterns input remaining state = .ok result) :
    ∃ labels,
      StringComputationRunTrace run patterns input state labels result ∧
        state.outcomes ++ labels = result.outcomes := by
  induction remaining generalizing earlier state result with
  | nil =>
      cases executed
      exact ⟨[], .nil state, by simp⟩
  | cons table remaining inductionHypothesis =>
      cases evaluated : run.evaluateTable patterns input state table with
      | error fault =>
          simp [CheckedStringComputationRun.executeTables, evaluated] at executed
      | ok completion =>
          simp [CheckedStringComputationRun.executeTables, evaluated] at executed
          have target := stringComputationRun_evaluateTable_target
            run patterns input state table completion evaluated
          have ready := stringComputationRun_table_ready
            run earlier remaining table split state stateTargets
          let next : StringComputationRunState :=
            { completed := state.completed ++ [completion] }
          have nextTargets :
              next.targetFields =
                (earlier ++ [table]).map (·.targetField) := by
            have stateTargets' :
                state.completed.map (·.targetField) =
                  earlier.map (·.targetField) := by
              simpa [StringComputationRunState.targetFields] using stateTargets
            simp [next, StringComputationRunState.targetFields,
              List.map_append, stateTargets', target]
          have nextSplit :
              run.tables = (earlier ++ [table]) ++ remaining := by
            simpa [List.append_assoc] using split
          obtain ⟨labels, trace, outcomes⟩ :=
            inductionHypothesis (earlier ++ [table]) next result
              nextSplit nextTargets executed
          refine ⟨(completion.targetField, completion.outcome) :: labels,
            .cons (.compute table ?_ ready.1 ready.2 completion evaluated) trace, ?_⟩
          · rw [split]
            simp
          · simpa [next, StringComputationRunState.outcomes,
              List.append_assoc] using outcomes

/-- Whole-plan successful execution therefore has a non-self-justifying relation trace with exactly the returned label list. -/
theorem stringComputationRun_execute_trace
    (run : CheckedStringComputationRun model)
    (patterns : PreparedFlatStringPatterns model compilePattern)
    (input : CheckedDocument model) (outcomes : List StringComputationRunLabel)
    (executed : run.execute patterns input = .ok outcomes) :
    ∃ result,
      StringComputationRunTrace run patterns input {} outcomes result ∧
        result.outcomes = outcomes := by
  cases runResult : run.executeTables patterns input run.tables {} with
  | error fault =>
      simp [CheckedStringComputationRun.execute, runResult] at executed
  | ok result =>
      have resultOutcomes : result.outcomes = outcomes := by
        simpa [CheckedStringComputationRun.execute, runResult] using executed
      obtain ⟨labels, trace, labelsEqual⟩ :=
        stringComputationRun_executeTables_trace run patterns input [] run.tables
          {} result (by simp) (by simp [StringComputationRunState.targetFields])
            runResult
      have labelsResult : labels = result.outcomes := by
        simpa [StringComputationRunState.outcomes] using labelsEqual
      rw [labelsResult, resultOutcomes] at trace
      exact ⟨result, trace, resultOutcomes⟩

end A12Kernel
