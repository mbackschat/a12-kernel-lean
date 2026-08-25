import A12Kernel.Elaboration.StringComputationRun

/-! # Checked String-computation run laws

These laws expose the three branches of the run's read policy and attribute structural failures to the table evaluated. Schedule relations and public result projections belong to later capsules.
-/

namespace A12Kernel

theorem stringComputationRun_read_pending
    (run : CheckedStringComputationRun model)
    (state : StringComputationRunState) (input : CheckedDocument model)
    (field : FieldId)
    (target : field ∈ run.targetFields)
    (pending : state.find? field = none) :
    (run.readPolicy state input).read field =
      StringDependencyCell.empty.checked := by
  simp [CheckedStringComputationRun.readPolicy, target, pending]

theorem stringComputationRun_read_completed
    (run : CheckedStringComputationRun model)
    (state : StringComputationRunState) (input : CheckedDocument model)
    (field : FieldId) (completion : StringComputationRunCompletion)
    (target : field ∈ run.targetFields)
    (found : state.find? field = some completion) :
    (run.readPolicy state input).read field =
      completion.dependencyCell.checked := by
  simp [CheckedStringComputationRun.readPolicy, target, found]

theorem stringComputationRun_read_input
    (run : CheckedStringComputationRun model)
    (state : StringComputationRunState) (input : CheckedDocument model)
    (field : FieldId)
    (ordinary : field ∉ run.targetFields) :
    (run.readPolicy state input).read field =
      input.stringComputationContext.read field := by
  simp [CheckedStringComputationRun.readPolicy, ordinary]

/-- Atomic String evaluation attributes either structural fault to the checked table it evaluated. -/
theorem stringComputationTable_evaluateCompletion_faultTarget
    (table : CheckedStringComputationTable model)
    (patterns : PreparedFlatStringPatterns model compilePattern)
    (context : StringComputationContext)
    (fault : StringComputationRunFault)
    (evaluated : table.evaluateCompletion patterns context = .error fault) :
    fault.target = table.targetField := by
  unfold CheckedStringComputationTable.evaluateCompletion at evaluated
  split at evaluated
  · cases evaluated
    rfl
  next preparedMatcher =>
    split at evaluated
    · cases evaluated
      rfl
    next outcomeValue =>
      split at evaluated
      · cases evaluated
        rfl
      · contradiction

/-- The homogeneous run's atomic wrapper preserves the failing table's target. -/
theorem stringComputationRun_evaluateTable_faultTarget
    (run : CheckedStringComputationRun model)
    (patterns : PreparedFlatStringPatterns model compilePattern)
    (input : CheckedDocument model)
    (state : StringComputationRunState)
    (table : CheckedStringComputationTable model)
    (fault : StringComputationRunFault)
    (evaluated : run.evaluateTable patterns input state table = .error fault) :
    fault.target = table.targetField :=
  stringComputationTable_evaluateCompletion_faultTarget
    table patterns (run.readPolicy state input) fault evaluated

private theorem stringComputationRun_executeTables_faultTarget
    (run : CheckedStringComputationRun model)
    (patterns : PreparedFlatStringPatterns model compilePattern)
    (input : CheckedDocument model)
    (tables : List (CheckedStringComputationTable model))
    (state : StringComputationRunState)
    (fault : StringComputationRunFault)
    (executed : run.executeTables patterns input tables state = .error fault) :
    fault.target ∈ tables.map (·.targetField) := by
  induction tables generalizing state with
  | nil =>
      simp only [CheckedStringComputationRun.executeTables] at executed
      cases executed
  | cons table remaining inductionHypothesis =>
      cases evaluation : run.evaluateTable patterns input state table with
      | error cause =>
          simp [CheckedStringComputationRun.executeTables, evaluation] at executed
          cases executed
          have target := stringComputationRun_evaluateTable_faultTarget
            run patterns input state table fault evaluation
          simp [target]
      | ok completion =>
          have remainingFault := inductionHypothesis
            (state := { completed := state.completed ++ [completion] }) (by
              simpa [CheckedStringComputationRun.executeTables, evaluation]
                using executed)
          simp [remainingFault]

/-- A public failing homogeneous String run names one of its own checked targets. -/
theorem stringComputationRun_execute_faultTarget
    (run : CheckedStringComputationRun model)
    (patterns : PreparedFlatStringPatterns model compilePattern)
    (input : CheckedDocument model)
    (fault : StringComputationRunFault)
    (executed : run.execute patterns input = .error fault) :
    fault.target ∈ run.targetFields := by
  cases result : run.executeTables patterns input run.tables {} with
  | error cause =>
      simp [CheckedStringComputationRun.execute, result] at executed
      cases executed
      simpa [CheckedStringComputationRun.targetFields] using
        stringComputationRun_executeTables_faultTarget
          run patterns input run.tables {} fault result
  | ok state =>
      simp [CheckedStringComputationRun.execute, result] at executed

end A12Kernel
