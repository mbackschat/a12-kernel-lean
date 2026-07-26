import A12Kernel.Elaboration.StringComputationRunRelation
import A12Kernel.Proofs.StringComputationRun

/-! # Checked String-run relation laws

The proof spine derives fixed-order trace soundness from the checked plan's two static certificates rather than defining the relation as executor equality.
-/

namespace A12Kernel

theorem fieldId_firstDuplicate_none_iff_nodup (fields : List FieldId) :
    FieldId.firstDuplicate? fields = none ↔ fields.Nodup := by
  induction fields with
  | nil => simp [FieldId.firstDuplicate?]
  | cons field remaining inductionHypothesis =>
      by_cases member : field ∈ remaining <;>
        simp [FieldId.firstDuplicate?, member, inductionHypothesis]

theorem checkedStringComputationTable_excludes_target
    (table : CheckedStringComputationTable model) :
    table.referencesField table.targetField = false := by
  simp only [CheckedStringComputationTable.referencesField,
    CheckedStringComputationAlternative.referencesField,
    table.first.guardExcludesTarget, table.first.expressionExcludesTarget,
    Bool.false_or, List.any_eq_false]
  intro alternative member
  simp [alternative.guardExcludesTarget, alternative.expressionExcludesTarget]

private theorem firstForwardStringDependency_none_tail
    (table : CheckedStringComputationTable model)
    (remaining : List (CheckedStringComputationTable model))
    (ordered : firstForwardStringDependency? (table :: remaining) = none) :
    firstForwardStringDependency? remaining = none := by
  unfold firstForwardStringDependency? at ordered
  cases found : remaining.find? fun later =>
      table.referencesField later.targetField with
  | none => simpa [found] using ordered
  | some later => simp [found] at ordered

private theorem firstForwardStringDependency_none_suffix
    (earlier suffix : List (CheckedStringComputationTable model))
    (ordered : firstForwardStringDependency? (earlier ++ suffix) = none) :
    firstForwardStringDependency? suffix = none := by
  induction earlier with
  | nil => simpa using ordered
  | cons table remaining inductionHypothesis =>
      apply inductionHypothesis
      exact firstForwardStringDependency_none_tail table (remaining ++ suffix) (by
        simpa using ordered)

private theorem firstForwardStringDependency_none_head
    (table : CheckedStringComputationTable model)
    (remaining : List (CheckedStringComputationTable model))
    (ordered : firstForwardStringDependency? (table :: remaining) = none)
    (later : CheckedStringComputationTable model) (member : later ∈ remaining) :
    table.referencesField later.targetField = false := by
  unfold firstForwardStringDependency? at ordered
  cases found : remaining.find? fun candidate =>
      table.referencesField candidate.targetField with
  | some candidate => simp [found] at ordered
  | none =>
      have notReferenced :=
        (List.find?_eq_none.mp found) later member
      cases referenced : table.referencesField later.targetField with
      | false => rfl
      | true => exact False.elim (notReferenced referenced)

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
      simp [CheckedStringComputationRun.evaluateTable, matcher] at evaluated
  | some targetMatcher =>
      cases outcome :
          table.evaluateOutcomeWithPattern targetMatcher
            (run.readPolicy state input) with
      | error fault =>
          simp [CheckedStringComputationRun.evaluateTable, matcher, outcome] at evaluated
      | ok result =>
          cases dependency : StringDependencyCell.ofOutcome result with
          | error fault =>
              simp [CheckedStringComputationRun.evaluateTable, matcher, outcome,
                dependency] at evaluated
          | ok cell =>
              simp [CheckedStringComputationRun.evaluateTable, matcher, outcome,
                dependency] at evaluated
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
        firstForwardStringDependency_none_suffix earlier (table :: remaining) (by
          simpa [split] using run.dependenciesOrdered)
      have notReferenced :=
        firstForwardStringDependency_none_head table remaining orderedSuffix
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
