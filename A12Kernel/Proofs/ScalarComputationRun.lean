import A12Kernel.Elaboration.ScalarComputationRun
import A12Kernel.Proofs.ComputationRunPlan
import A12Kernel.Proofs.FieldId
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
  | dateTimeDayShift operation _ =>
      cases result : operation.evaluateOutcome (run.documentFor state input) with
      | error cause =>
          simp [CheckedScalarComputationRun.evaluateStep, result] at evaluated
          subst fault
          exact ⟨rfl, rfl⟩
      | ok outcome =>
          cases cell : CheckedScalarComputationRun.dateTimeDependencyCell model
              operation.target.checked.target.id outcome with
          | error cause =>
              simp [CheckedScalarComputationRun.evaluateStep, result, cell, Except.map,
                Except.mapError] at evaluated
              subst fault
              exact ⟨rfl, rfl⟩
          | ok readCell =>
              simp [CheckedScalarComputationRun.evaluateStep, result, cell, Except.map,
                Except.mapError] at evaluated
  | dateTimeSubdayShift operation _ =>
      cases result : operation.evaluateOutcome (run.documentFor state input) with
      | error cause =>
          simp [CheckedScalarComputationRun.evaluateStep, result] at evaluated
          subst fault
          exact ⟨rfl, rfl⟩
      | ok outcome =>
          cases cell : CheckedScalarComputationRun.dateTimeDependencyCell model
              operation.target.checked.target.id outcome with
          | error cause =>
              simp [CheckedScalarComputationRun.evaluateStep, result, cell, Except.map,
                Except.mapError] at evaluated
              subst fault
              exact ⟨rfl, rfl⟩
          | ok readCell =>
              simp [CheckedScalarComputationRun.evaluateStep, result, cell, Except.map,
                Except.mapError] at evaluated

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

/-- A certified plan runs exactly its authored steps, typed operations included, in some order. -/
theorem scalarComputationPlan_executionSteps_perm
    (plan : CheckedScalarComputationPlan model) :
    plan.execution.steps.Perm plan.authored := by
  rw [plan.executionUsesSelectedSteps]
  exact computationAuthoredOrder_perm _ _ _ _

/-- A run refused for a forward read passed the duplicate gate and holds that read. -/
theorem certifyScalarComputationRunWithSteps_forwardDependency
    (steps : List (CheckedScalarComputationStep model)) (step reads : FieldId)
    (refused :
      certifyScalarComputationRunWithSteps steps = .error (.forwardDependency step reads)) :
    FieldId.firstDuplicate? (steps.map (·.targetField)) = none ∧
      firstForwardScalarComputationDependency? steps = some (step, reads) := by
  cases steps with
  | nil => simp [certifyScalarComputationRunWithSteps] at refused
  | cons first remaining =>
    dsimp only [certifyScalarComputationRunWithSteps] at refused
    split at refused
    · simp at refused
    · split at refused
      · simp at refused
      · rename_i noDuplicate
        split at refused
        · rename_i found forward
          simp only [Except.error.injEq, ScalarComputationRunPlanError.forwardDependency.injEq]
            at refused
          obtain ⟨rfl, rfl⟩ := refused
          exact ⟨noDuplicate, forward⟩
        · simp at refused

/-- A plan refused as a cycle has read-closed steps: the refusal never falls on an acyclic plan. -/
theorem certifyScalarComputationPlan_cycle_readClosed
    (steps : List (CheckedScalarComputationStep model)) (step reads : FieldId)
    (refused : certifyScalarComputationPlan steps = .error (.cycle step reads)) :
    ∃ stuck, ComputationStepsReadClosed CheckedScalarComputationStep.targetField
        CheckedScalarComputationStep.referencesField stuck ∧
      ∀ member ∈ stuck, member ∈ steps := by
  unfold certifyScalarComputationPlan at refused
  split at refused
  · simp at refused
  · simp at refused
  · simp at refused
  · rename_i step' reads' certified
    simp only [Except.error.injEq, ScalarComputationPlanError.cycle.injEq] at refused
    obtain ⟨rfl, rfl⟩ := refused
    obtain ⟨noDuplicate, forward⟩ :=
      certifyScalarComputationRunWithSteps_forwardDependency _ step' reads' certified
    have orderPerm := computationAuthoredOrder_perm CheckedScalarComputationStep.targetField
      CheckedScalarComputationStep.referencesField steps.length steps
    have unique : (steps.map (·.targetField)).Nodup :=
      (orderPerm.map _).nodup_iff.mp ((fieldId_firstDuplicate_none_iff_nodup _).mp noDuplicate)
    exact computationAuthoredOrder_forward_readClosed _ _ steps.length steps
      (Nat.le_refl _) unique (by
        unfold scalarComputationAuthoredExecutionSteps firstForwardScalarComputationDependency?
          at forward
        rw [forward]
        simp)
  · simp at refused

/-- A certified plan's authored steps hold no read-closed steps, so every cyclic plan is refused. -/
theorem scalarComputationPlan_not_readClosed
    (plan : CheckedScalarComputationPlan model)
    (stuck : List (CheckedScalarComputationStep model))
    (closed : ComputationStepsReadClosed CheckedScalarComputationStep.targetField
      CheckedScalarComputationStep.referencesField stuck) :
    ¬ ∀ member ∈ stuck, member ∈ plan.authored := fun within =>
  computationSteps_not_readClosed _ _ plan.execution.steps stuck
    plan.execution.dependenciesOrdered closed fun member memberStuck =>
      (scalarComputationPlan_executionSteps_perm plan).mem_iff.mpr (within member memberStuck)

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
