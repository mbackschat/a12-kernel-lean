import A12Kernel.Elaboration.NumericComputation.RunRelation
import A12Kernel.Proofs.ComputationRunPlan
import A12Kernel.Proofs.NumericComputationRun
import A12Kernel.Proofs.FieldId

/-! # Checked Number-run relation laws -/

namespace A12Kernel

/-- Every successful step label names a target owned by the checked run. -/
theorem numericComputationRunStep_target_mem
    (step : NumericComputationRunStep run world input state label next) :
    label.1 ∈ run.targetFields := by
  cases step with
  | compute table member pending enabled completion evaluated =>
      rw [numericComputationRun_evaluateTable_target
        run world input state table completion evaluated]
      exact List.mem_map.mpr ⟨table, member, rfl⟩

/-- Checked Numeric expressions cannot read their own target. -/
private theorem checkedNumericComputationOperation_excludes_target
    (operation : CheckedNumericTargetComputationOperation model) :
    operation.referencesField operation.operation.core.target.id = false := by
  have wellFormed := operation.operation.wellFormed
  unfold NumericComputationOperation.WellFormed
    NumericComputationOperation.wellFormedBool at wellFormed
  simp only [Bool.and_eq_true] at wellFormed
  have referenceNegated := wellFormed.1.1.1.2
  change operation.operation.core.expression.anyAtom
    (CheckedNumericComputationAtom.references model
      operation.operation.core.target.id) = false
  cases referenced : operation.operation.core.expression.anyAtom
      (CheckedNumericComputationAtom.references model
        operation.operation.core.target.id) with
  | false => rfl
  | true => simp [referenced] at referenceNegated

private theorem checkedNumericComputationAlternative_excludes_target
    (alternative :
      CheckedNumericComputationAlternative model target policy) :
    (alternative.toSelectable.precondition.referencesField target ||
        alternative.toSelectable.operation.referencesField target) = false := by
  have operationExcludes :
      alternative.operation.referencesField target = false := by
    let references := fun field =>
      alternative.operation.referencesField field
    calc
      references target =
          references alternative.operation.operation.core.target.id :=
        (congrArg references alternative.targetMatches).symm
      _ = false :=
        checkedNumericComputationOperation_excludes_target
          alternative.operation
  simp [CheckedNumericComputationAlternative.toSelectable,
    alternative.guardExcludesTarget, operationExcludes]

theorem checkedNumericComputationTable_excludes_target
    (table : CheckedNumericComputationTable model) :
    table.referencesField table.targetField = false := by
  simp [CheckedNumericComputationTable.referencesField,
    CheckedNumericComputationTable.selectableAlternatives,
    CheckedNumericComputationTable.checkedAlternatives,
    checkedNumericComputationAlternative_excludes_target]

private theorem numericComputationRun_table_ready
    (run : CheckedNumericComputationRun model)
    (earlier remaining : List (CheckedNumericComputationTable model))
    (table : CheckedNumericComputationTable model)
    (split : run.tables = earlier ++ table :: remaining)
    (state : NumericComputationRunState)
    (stateTargets :
      state.targetFields = earlier.map (·.targetField)) :
    table.targetField ∉ state.targetFields ∧
      NumericComputationDependenciesEnabled run table state := by
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
      rw [checkedNumericComputationTable_excludes_target] at referenced
      contradiction
    · have orderedSuffix :
          firstForwardNumericDependency? (table :: remaining) = none :=
        by
          have generic :=
            firstForwardComputationDependency_none_suffix
              (fun candidate : CheckedNumericComputationTable model =>
                candidate.targetField)
              (fun candidate field =>
                candidate.referencesField field)
              earlier (table :: remaining) (by
                simpa [firstForwardNumericDependency?, split]
                  using run.dependenciesOrdered)
          simpa [firstForwardNumericDependency?] using generic
      have notReferenced :=
        firstForwardComputationDependency_none_head
          (fun candidate : CheckedNumericComputationTable model =>
            candidate.targetField)
          (fun candidate field => candidate.referencesField field)
          table remaining (by
            simpa [firstForwardNumericDependency?] using orderedSuffix)
          dependency inRemaining
      rw [notReferenced] at referenced
      contradiction

/-- Successful fixed-order suffix execution is a trace of independently enabled steps with exactly the newly appended labels. -/
theorem numericComputationRun_executeTables_trace
    (run : CheckedNumericComputationRun model)
    (world : World) (input : CheckedDocument model)
    (earlier remaining : List (CheckedNumericComputationTable model))
    (state result : NumericComputationRunState)
    (split : run.tables = earlier ++ remaining)
    (stateTargets : state.targetFields = earlier.map (·.targetField))
    (executed :
      run.executeTables world input remaining state = .ok result) :
    ∃ labels,
      NumericComputationRunTrace run world input state labels result ∧
        state.outcomes ++ labels = result.outcomes := by
  induction remaining generalizing earlier state result with
  | nil =>
      cases executed
      exact ⟨[], .nil state, by simp⟩
  | cons table remaining inductionHypothesis =>
      cases evaluated :
          run.evaluateTable world input state table with
      | error fault =>
          simp [CheckedNumericComputationRun.executeTables, evaluated] at executed
      | ok completion =>
          simp [CheckedNumericComputationRun.executeTables, evaluated] at executed
          have target := numericComputationRun_evaluateTable_target
            run world input state table completion evaluated
          have ready := numericComputationRun_table_ready
            run earlier remaining table split state stateTargets
          let next : NumericComputationRunState :=
            { completed := state.completed ++ [completion] }
          have nextTargets :
              next.targetFields =
                (earlier ++ [table]).map (·.targetField) := by
            have stateTargets' :
                state.completed.map (·.targetField) =
                  earlier.map (·.targetField) := by
              simpa [NumericComputationRunState.targetFields] using stateTargets
            simp [next, NumericComputationRunState.targetFields,
              List.map_append, stateTargets', target]
          have nextSplit :
              run.tables = (earlier ++ [table]) ++ remaining := by
            simpa [List.append_assoc] using split
          obtain ⟨labels, trace, outcomes⟩ :=
            inductionHypothesis (earlier ++ [table]) next result
              nextSplit nextTargets executed
          refine ⟨(completion.targetField, completion.outcome) :: labels,
            .cons (.compute table ?_ ready.1 ready.2 completion evaluated)
              trace, ?_⟩
          · rw [split]
            simp
          · simpa [next, NumericComputationRunState.outcomes,
              List.append_assoc] using outcomes

/-- Successful fixed execution therefore has a non-self-justifying relation trace carrying exactly its returned labels. -/
theorem numericComputationRun_execute_trace
    (run : CheckedNumericComputationRun model)
    (world : World) (input : CheckedDocument model)
    (outcomes : List NumericComputationRunLabel)
    (executed : run.execute world input = .ok outcomes) :
    ∃ result,
      NumericComputationRunTrace run world input {} outcomes result ∧
        result.outcomes = outcomes := by
  cases runResult : run.executeTables world input run.tables {} with
  | error fault =>
      simp [CheckedNumericComputationRun.execute, runResult] at executed
  | ok result =>
      have resultOutcomes : result.outcomes = outcomes := by
        simpa [CheckedNumericComputationRun.execute, runResult] using executed
      obtain ⟨labels, trace, labelsEqual⟩ :=
        numericComputationRun_executeTables_trace
          run world input [] run.tables
          {} result (by simp)
            (by simp [NumericComputationRunState.targetFields]) runResult
      have labelsResult : labels = result.outcomes := by
        simpa [NumericComputationRunState.outcomes] using labelsEqual
      rw [labelsResult, resultOutcomes] at trace
      exact ⟨result, trace, resultOutcomes⟩

end A12Kernel
