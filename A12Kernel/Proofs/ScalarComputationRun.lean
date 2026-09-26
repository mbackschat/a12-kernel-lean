import A12Kernel.Elaboration.ScalarComputationRun
import A12Kernel.Proofs.NumericComputationRun
import A12Kernel.Proofs.StringComputationRun

/-! # Finite mixed scalar computation-run laws

These laws expose consumer-specific pending/completed/input reads and prove that atomic success or structural failure retains the selected table's family and target rather than lowering to a common result.
-/

namespace A12Kernel

theorem scalarComputationRun_stringRead_pending
    (run : CheckedScalarComputationRun model)
    (state : ScalarComputationRunState)
    (input : CheckedDocument model)
    (field : FieldId)
    (target : field ∈ run.targetFields)
    (pending : state.find? field = none) :
    (run.stringContext state input).read field =
      StringDependencyCell.empty.checked := by
  simp [CheckedScalarComputationRun.stringContext, target, pending]

theorem scalarComputationRun_stringRead_completed
    (run : CheckedScalarComputationRun model)
    (state : ScalarComputationRunState)
    (input : CheckedDocument model)
    (field : FieldId)
    (completion : ScalarComputationCompletion)
    (found : state.find? field = some completion) :
    (run.stringContext state input).read field =
      completion.stringCell := by
  simp [CheckedScalarComputationRun.stringContext, found]

theorem scalarComputationRun_stringRead_input
    (run : CheckedScalarComputationRun model)
    (state : ScalarComputationRunState)
    (input : CheckedDocument model)
    (field : FieldId)
    (pending : state.find? field = none)
    (ordinary : field ∉ run.targetFields) :
    (run.stringContext state input).read field =
      input.stringComputationContext.read field := by
  simp [CheckedScalarComputationRun.stringContext, pending, ordinary]

theorem scalarComputationRun_numberRead_pending
    (run : CheckedScalarComputationRun model)
    (world : World)
    (state : ScalarComputationRunState)
    (input : CheckedDocument model)
    (field : FieldId)
    (target : field ∈ run.targetFields)
    (pending : state.find? field = none) :
    (run.numberContext world state input).read field =
      (NumericDependencyCell.ofObservation .empty).checked := by
  simp [CheckedScalarComputationRun.numberContext, target, pending]

theorem scalarComputationRun_numberRead_completed
    (run : CheckedScalarComputationRun model)
    (world : World)
    (state : ScalarComputationRunState)
    (input : CheckedDocument model)
    (field : FieldId)
    (completion : ScalarComputationCompletion)
    (found : state.find? field = some completion) :
    (run.numberContext world state input).read field =
      completion.numberCell := by
  simp [CheckedScalarComputationRun.numberContext, found]

theorem scalarComputationRun_numberRead_input
    (run : CheckedScalarComputationRun model)
    (world : World)
    (state : ScalarComputationRunState)
    (input : CheckedDocument model)
    (field : FieldId)
    (pending : state.find? field = none)
    (ordinary : field ∉ run.targetFields) :
    (run.numberContext world state input).read field =
      input.flatContext.read field := by
  simp [CheckedScalarComputationRun.numberContext,
    CheckedDocument.scalarComputationContext, pending, ordinary]

theorem scalarComputationRun_numberContext_world
    (run : CheckedScalarComputationRun model)
    (world : World)
    (state : ScalarComputationRunState)
    (input : CheckedDocument model) :
    (run.numberContext world state input).world = some world := by
  rfl

/-- Atomic String evaluation retains the String completion constructor exactly. -/
theorem scalarComputationRun_evaluateStringStep
    (run : CheckedScalarComputationRun model)
    (world : World)
    (patterns : PreparedFlatStringPatterns model compilePattern)
    (input : CheckedDocument model)
    (state : ScalarComputationRunState)
    (table : CheckedStringComputationTable model)
    (completion : StringComputationRunCompletion)
    (evaluated :
      table.evaluateCompletion patterns
        (run.stringContext state input) = .ok completion) :
    run.evaluateStep world patterns input state (.string table) =
      .ok (.string completion) := by
  simp [CheckedScalarComputationRun.evaluateStep, evaluated]

/-- Atomic Number evaluation retains the Number completion constructor exactly. -/
theorem scalarComputationRun_evaluateNumberStep
    (run : CheckedScalarComputationRun model)
    (world : World)
    (patterns : PreparedFlatStringPatterns model compilePattern)
    (input : CheckedDocument model)
    (state : ScalarComputationRunState)
    (table : CheckedNumericComputationTable model)
    (completion : NumericComputationRunCompletion)
    (evaluated :
      table.evaluateCompletion
        (run.numberContext world state input) = .ok completion) :
    run.evaluateStep world patterns input state (.number table) =
      .ok (.number completion) := by
  simp [CheckedScalarComputationRun.evaluateStep, evaluated]

/-- Atomic mixed evaluation preserves both the selected family's constructor and its own failing target. -/
theorem scalarComputationRun_evaluateStep_faultIdentity
    (run : CheckedScalarComputationRun model)
    (world : World)
    (patterns : PreparedFlatStringPatterns model compilePattern)
    (input : CheckedDocument model)
    (state : ScalarComputationRunState)
    (step : CheckedScalarComputationStep model)
    (fault : ScalarComputationRunFault)
    (evaluated :
      run.evaluateStep world patterns input state step = .error fault) :
    fault.target = step.targetField ∧ fault.targetKind = step.targetKind := by
  cases step with
  | string table =>
      cases result : table.evaluateCompletion patterns
          (run.stringContext state input) with
      | error cause =>
          simp [CheckedScalarComputationRun.evaluateStep, result] at evaluated
          subst fault
          constructor
          · exact stringComputationTable_evaluateCompletion_faultTarget
              table patterns (run.stringContext state input) cause result
          · rfl
      | ok completion =>
          simp [CheckedScalarComputationRun.evaluateStep, result] at evaluated
  | number table =>
      cases result : table.evaluateCompletion
          (run.numberContext world state input) with
      | error cause =>
          simp [CheckedScalarComputationRun.evaluateStep, result] at evaluated
          subst fault
          constructor
          · exact numericComputationTable_evaluateCompletion_faultTarget
              table (run.numberContext world state input) cause result
          · rfl
      | ok completion =>
          simp [CheckedScalarComputationRun.evaluateStep, result] at evaluated

/-- A failing mixed suffix attributes its structural fault to one of the exact typed steps it was given. -/
private theorem scalarComputationRun_executeSteps_faultTarget
    (run : CheckedScalarComputationRun model)
    (world : World)
    (patterns : PreparedFlatStringPatterns model compilePattern)
    (input : CheckedDocument model)
    (steps : List (CheckedScalarComputationStep model))
    (state : ScalarComputationRunState)
    (fault : ScalarComputationRunFault)
    (executed :
      run.executeSteps world patterns input steps state = .error fault) :
    fault.target ∈ steps.map (·.targetField) := by
  induction steps generalizing state with
  | nil =>
      simp only [CheckedScalarComputationRun.executeSteps] at executed
      cases executed
  | cons step remaining inductionHypothesis =>
      cases evaluation : run.evaluateStep world patterns input state step with
      | error cause =>
          rw [CheckedScalarComputationRun.executeSteps, evaluation] at executed
          change Except.error cause = Except.error fault at executed
          cases executed
          have target := (scalarComputationRun_evaluateStep_faultIdentity
            run world patterns input state step fault evaluation
          ).1
          simp [target]
      | ok completion =>
          have remainingExecuted :
              run.executeSteps world patterns input remaining {
                completed := state.completed ++ [completion]
              } = .error fault := by
            rw [CheckedScalarComputationRun.executeSteps, evaluation] at executed
            change run.executeSteps world patterns input remaining {
              completed := state.completed ++ [completion]
            } = .error fault at executed
            exact executed
          have remainingFault := inductionHypothesis
            (state := { completed := state.completed ++ [completion] })
            remainingExecuted
          simp [remainingFault]

/-- A public failing mixed run names one of its own checked targets without erasing the String-or-Number fault constructor. -/
theorem scalarComputationRun_execute_faultTarget
    (run : CheckedScalarComputationRun model)
    (world : World)
    (patterns : PreparedFlatStringPatterns model compilePattern)
    (input : CheckedDocument model)
    (fault : ScalarComputationRunFault)
    (executed : run.execute world patterns input = .error fault) :
    fault.target ∈ run.targetFields := by
  cases result : run.executeSteps world patterns input run.steps {} with
  | error cause =>
      rw [CheckedScalarComputationRun.execute, result] at executed
      change Except.error cause = Except.error fault at executed
      cases executed
      simpa [CheckedScalarComputationRun.targetFields] using
        scalarComputationRun_executeSteps_faultTarget
          run world patterns input run.steps {} fault result
  | ok state =>
      rw [CheckedScalarComputationRun.execute, result] at executed
      change Except.ok state.outcomes = Except.error fault at executed
      cases executed

/-- Selecting a ready step removes it from the scanned list and changes nothing else. -/
theorem firstReadyScalarComputationStep_perm
    (pending : List (CheckedScalarComputationStep model)) :
    ∀ (scan rest : List (CheckedScalarComputationStep model))
      (ready : CheckedScalarComputationStep model),
      firstReadyScalarComputationStep? pending scan = some (ready, rest) →
        (ready :: rest).Perm scan := by
  intro scan
  induction scan with
  | nil => intro _ _ selected; simp [firstReadyScalarComputationStep?] at selected
  | cons step tail ih =>
    intro rest ready selected
    unfold firstReadyScalarComputationStep? at selected
    split at selected
    · simp only [Option.some.injEq, Prod.mk.injEq] at selected
      obtain ⟨rfl, rfl⟩ := selected
      exact List.Perm.refl _
    · cases hTail : firstReadyScalarComputationStep? pending tail with
      | none => simp [hTail] at selected
      | some found =>
        obtain ⟨found, remaining⟩ := found
        simp only [hTail, Option.map_some, Option.some.injEq, Prod.mk.injEq] at selected
        obtain ⟨sameReady, sameRest⟩ := selected
        rw [← sameReady, ← sameRest]
        exact (List.Perm.swap _ _ remaining).trans
          (List.Perm.cons step (ih remaining found hTail))

/-- Ordering only reorders: every authored step is run exactly once. -/
theorem scalarComputationAuthoredOrder_perm :
    ∀ (fuel : Nat) (pending : List (CheckedScalarComputationStep model)),
      (scalarComputationAuthoredOrder fuel pending).Perm pending := by
  intro fuel
  induction fuel with
  | zero => intro pending; exact List.Perm.refl _
  | succ fuel ih =>
    intro pending
    unfold scalarComputationAuthoredOrder
    split
    · exact List.Perm.refl _
    · rename_i ready remaining selected
      exact (List.Perm.cons ready (ih remaining)).trans
        (firstReadyScalarComputationStep_perm pending pending remaining ready selected)

/-- A certified plan runs exactly its authored steps, typed operations included, in some order. -/
theorem scalarComputationPlan_executionSteps_perm
    (plan : CheckedScalarComputationPlan model) :
    plan.execution.steps.Perm plan.authored := by
  rw [plan.executionUsesSelectedSteps]
  exact scalarComputationAuthoredOrder_perm _ _

/-- Two authored steps where the first reads the second's target and the second does not read the
first's run producer first: the two-step case of the plan order. -/
theorem scalarComputationAuthoredExecutionSteps_pair_forward
    (first second : CheckedScalarComputationStep model)
    (distinct : first.targetField ≠ second.targetField)
    (forward : first.referencesField second.targetField = true)
    (backward : second.referencesField first.targetField = false) :
    scalarComputationAuthoredExecutionSteps [first, second] = [second, first] := by
  have firstSecond := beq_false_of_ne distinct
  have secondFirst := beq_false_of_ne (Ne.symm distinct)
  simp [scalarComputationAuthoredExecutionSteps, scalarComputationAuthoredOrder,
    firstReadyScalarComputationStep?, firstSecond, secondFirst, forward, backward]

/-- Two authored steps where the first does not read the second's target keep authored order. -/
theorem scalarComputationAuthoredExecutionSteps_pair_preserved
    (first second : CheckedScalarComputationStep model)
    (forward : first.referencesField second.targetField = false) :
    scalarComputationAuthoredExecutionSteps [first, second] = [first, second] := by
  simp [scalarComputationAuthoredExecutionSteps, scalarComputationAuthoredOrder,
    firstReadyScalarComputationStep?, forward]

/-- Plan execution is exactly the established typed mixed-run execution. -/
theorem scalarComputationPlan_execute
    (plan : CheckedScalarComputationPlan model)
    (world : World)
    (patterns : PreparedFlatStringPatterns model compilePattern)
    (input : CheckedDocument model) :
    plan.execute world patterns input =
      plan.execution.execute world patterns input := by
  rfl

/-- Pre-schedule analysis preserves every candidate target exactly and in authored order. -/
@[simp] theorem analyzeScalarComputationSteps_targets
    (steps : List (CheckedScalarComputationStep model)) :
    (analyzeScalarComputationSteps steps).map (·.targetField) =
      steps.map (·.targetField) := by
  simp [analyzeScalarComputationSteps,
    CheckedScalarComputationStep.dependencyAnalysis]

/-- Pre-schedule analysis preserves every candidate target family exactly and in authored order. -/
@[simp] theorem analyzeScalarComputationSteps_kinds
    (steps : List (CheckedScalarComputationStep model)) :
    (analyzeScalarComputationSteps steps).map (·.targetKind) =
      steps.map (·.targetKind) := by
  simp [analyzeScalarComputationSteps,
    CheckedScalarComputationStep.dependencyAnalysis]

/-- Pre-schedule analysis preserves each candidate's complete raw dependency list exactly and in authored order. -/
@[simp] theorem analyzeScalarComputationSteps_dependencies
    (steps : List (CheckedScalarComputationStep model)) :
    (analyzeScalarComputationSteps steps).map (·.fieldDependencies) =
      steps.map (·.fieldDependencies) := by
  simp [analyzeScalarComputationSteps,
    CheckedScalarComputationStep.dependencyAnalysis]

end A12Kernel
