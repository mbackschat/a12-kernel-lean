import A12Kernel.Elaboration.NumericComputation.Run

/-! # Checked Number computation-run laws -/

namespace A12Kernel

theorem numericComputationRun_read_pending
    (run : CheckedNumericComputationRun model)
    (state : NumericComputationRunState) (input : CheckedDocument model)
    (field : FieldId) (target : field ∈ run.targetFields)
    (pending : state.find? field = none) :
    (run.readPolicy state input).read field =
      (NumericDependencyCell.ofObservation .empty).checked := by
  simp [CheckedNumericComputationRun.readPolicy, target, pending]

theorem numericComputationRun_read_completed
    (run : CheckedNumericComputationRun model)
    (state : NumericComputationRunState) (input : CheckedDocument model)
    (field : FieldId) (completion : NumericComputationRunCompletion)
    (target : field ∈ run.targetFields)
    (found : state.find? field = some completion) :
    (run.readPolicy state input).read field =
      (NumericDependencyCell.ofOutcome completion.outcome).checked := by
  simp [CheckedNumericComputationRun.readPolicy, target, found]

theorem numericComputationRun_read_input
    (run : CheckedNumericComputationRun model)
    (state : NumericComputationRunState) (input : CheckedDocument model)
    (field : FieldId) (ordinary : field ∉ run.targetFields) :
    (run.readPolicy state input).read field =
      input.flatContext.read field := by
  simp [CheckedNumericComputationRun.readPolicy, ordinary]

/-- Successful atomic evaluation retains exactly the checked table's target. -/
theorem numericComputationRun_evaluateTable_target
    (run : CheckedNumericComputationRun model)
    (world : World) (input : CheckedDocument model)
    (state : NumericComputationRunState)
    (table : CheckedNumericComputationTable model)
    (completion : NumericComputationRunCompletion)
    (evaluated :
      run.evaluateTable world input state table = .ok completion) :
    completion.targetField = table.targetField := by
  cases result :
      table.evaluate ((run.readPolicy state input).withWorld world) with
  | error fault =>
      simp [CheckedNumericComputationRun.evaluateTable,
        CheckedNumericComputationTable.evaluateCompletion, result] at evaluated
  | ok checked =>
      cases checked with
      | unsupported fault =>
          simp [CheckedNumericComputationRun.evaluateTable,
            CheckedNumericComputationTable.evaluateCompletion, result] at evaluated
      | supported outcome =>
          simp [CheckedNumericComputationRun.evaluateTable,
            CheckedNumericComputationTable.evaluateCompletion, result] at evaluated
          cases evaluated
          rfl

/-- Successful suffix execution appends completion targets in exactly the supplied table order. -/
private theorem numericComputationRun_executeTables_targetOrder
    (run : CheckedNumericComputationRun model)
    (world : World) (input : CheckedDocument model)
    (tables : List (CheckedNumericComputationTable model))
    (state result : NumericComputationRunState)
    (executed :
      run.executeTables world input tables state = .ok result) :
    result.completed.map (·.targetField) =
      state.completed.map (·.targetField) ++
        tables.map (·.targetField) := by
  induction tables generalizing state result with
  | nil =>
      simp only [CheckedNumericComputationRun.executeTables] at executed
      cases executed
      simp
  | cons table remaining inductionHypothesis =>
      cases evaluation :
          run.evaluateTable world input state table with
      | error fault =>
          simp [CheckedNumericComputationRun.executeTables, evaluation] at executed
      | ok completion =>
          have target :=
            numericComputationRun_evaluateTable_target
              run world input state table completion evaluation
          have order := inductionHypothesis
            (state := {
              completed := state.completed ++ [completion]
            }) (result := result) (by
              simpa [CheckedNumericComputationRun.executeTables, evaluation]
                using executed)
          simpa [List.map_append, target, List.append_assoc] using order

/-- The public successful run preserves supplied target order exactly. -/
theorem numericComputationRun_execute_targetOrder
    (run : CheckedNumericComputationRun model)
    (world : World) (input : CheckedDocument model)
    (outcomes : List (FieldId × NumericTargetOutcome))
    (executed : run.execute world input = .ok outcomes) :
    outcomes.map (·.1) = run.targetFields := by
  cases result : run.executeTables world input run.tables {} with
  | error fault =>
      simp [CheckedNumericComputationRun.execute, result] at executed
  | ok state =>
      simp [CheckedNumericComputationRun.execute, result] at executed
      subst outcomes
      simpa [NumericComputationRunState.outcomes,
        CheckedNumericComputationRun.targetFields, List.map_map,
        Function.comp_def] using
        numericComputationRun_executeTables_targetOrder
          run world input run.tables {} state result

/-- Unique checked plan targets make every successful public completion insert-once. -/
theorem numericComputationRun_execute_targetsUnique
    (run : CheckedNumericComputationRun model)
    (world : World) (input : CheckedDocument model)
    (outcomes : List (FieldId × NumericTargetOutcome))
    (executed : run.execute world input = .ok outcomes) :
    FieldId.firstDuplicate? (outcomes.map (·.1)) = none := by
  rw [numericComputationRun_execute_targetOrder
    run world input outcomes executed]
  simpa [CheckedNumericComputationRun.targetFields] using run.uniqueTargets

end A12Kernel
