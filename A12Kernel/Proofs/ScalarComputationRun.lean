import A12Kernel.Elaboration.ScalarComputationRun
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

/-- A selected step reads no target of another pending step. -/
theorem firstReadyScalarComputationStep_ready
    (pending : List (CheckedScalarComputationStep model)) :
    ∀ (scan rest : List (CheckedScalarComputationStep model))
      (ready : CheckedScalarComputationStep model),
      firstReadyScalarComputationStep? pending scan = some (ready, rest) →
        ∀ other ∈ pending, other.targetField ≠ ready.targetField →
          ready.referencesField other.targetField = false := by
  intro scan
  induction scan with
  | nil => intro _ _ selected; simp [firstReadyScalarComputationStep?] at selected
  | cons step tail ih =>
    intro rest ready selected other member distinct
    unfold firstReadyScalarComputationStep? at selected
    split at selected
    · rename_i allReady
      simp only [Option.some.injEq, Prod.mk.injEq] at selected
      obtain ⟨rfl, rfl⟩ := selected
      have := List.all_eq_true.mp allReady other member
      simpa [beq_false_of_ne distinct] using this
    · cases hTail : firstReadyScalarComputationStep? pending tail with
      | none => simp [hTail] at selected
      | some found =>
        obtain ⟨found, remaining⟩ := found
        simp only [hTail, Option.map_some, Option.some.injEq, Prod.mk.injEq] at selected
        rw [← selected.1]
        exact ih remaining found hTail other member (selected.1 ▸ distinct)

/-- When no step is ready, every scanned step reads the target of another pending step. -/
theorem firstReadyScalarComputationStep_none
    (pending : List (CheckedScalarComputationStep model)) :
    ∀ scan : List (CheckedScalarComputationStep model),
      firstReadyScalarComputationStep? pending scan = none →
        ∀ step ∈ scan, ∃ other ∈ pending,
          other.targetField ≠ step.targetField ∧ step.referencesField other.targetField = true := by
  intro scan
  induction scan with
  | nil => intro _ step member; simp at member
  | cons head tail ih =>
    intro stuck step member
    unfold firstReadyScalarComputationStep? at stuck
    split at stuck
    · simp at stuck
    · rename_i notReady
      rcases List.mem_cons.mp member with rfl | member
      · have blockedBy : ∃ other ∈ pending,
            (other.targetField == step.targetField || !step.referencesField other.targetField) =
              false := by
          simpa [List.all_eq_true] using notReady
        obtain ⟨other, otherMember, blocked⟩ := blockedBy
        have blocked : other.targetField ≠ step.targetField ∧
            step.referencesField other.targetField = true := by
          simpa using blocked
        exact ⟨other, otherMember, blocked⟩
      · cases hTail : firstReadyScalarComputationStep? pending tail with
        | none => exact ih hTail step member
        | some found => simp [hTail] at stuck

/-- Where the plan order keeps a forward read, some of the ordered steps are read-closed. -/
theorem scalarComputationAuthoredOrder_forward_readClosed :
    ∀ (fuel : Nat) (pending : List (CheckedScalarComputationStep model)),
      pending.length ≤ fuel →
      (pending.map (·.targetField)).Nodup →
      firstForwardScalarComputationDependency? (scalarComputationAuthoredOrder fuel pending) ≠ none →
        ∃ stuck, ScalarComputationStepsReadClosed stuck ∧ ∀ step ∈ stuck, step ∈ pending := by
  intro fuel
  induction fuel with
  | zero =>
    intro pending short _ forward
    have : pending = [] := List.eq_nil_of_length_eq_zero (Nat.le_zero.mp short)
    subst this
    simp [scalarComputationAuthoredOrder, firstForwardScalarComputationDependency?,
      firstForwardComputationDependency?] at forward
  | succ fuel ih =>
    intro pending short unique forward
    unfold scalarComputationAuthoredOrder at forward
    split at forward
    · rename_i noneReady
      refine ⟨pending, ⟨?_, firstReadyScalarComputationStep_none pending pending noneReady⟩,
        fun _ member => member⟩
      intro empty
      subst empty
      simp [firstForwardScalarComputationDependency?, firstForwardComputationDependency?] at forward
    · rename_i ready remaining selected
      have selectedPerm := firstReadyScalarComputationStep_perm pending pending remaining ready selected
      have orderPerm := scalarComputationAuthoredOrder_perm fuel remaining
      have uniqueSelected : ((ready :: remaining).map (·.targetField)).Nodup :=
        (selectedPerm.map _).nodup_iff.mpr unique
      have readyAbsent : ready.targetField ∉ remaining.map (·.targetField) :=
        (List.nodup_cons.mp uniqueSelected).1
      unfold firstForwardScalarComputationDependency? firstForwardComputationDependency? at forward
      split at forward
      · rename_i later found
        have laterMember := List.mem_of_find?_eq_some found
        have reads := List.find?_some found
        have laterRemaining := orderPerm.mem_iff.mp laterMember
        have laterPending := selectedPerm.mem_iff.mp (List.mem_cons_of_mem ready laterRemaining)
        have distinct : later.targetField ≠ ready.targetField := fun same =>
          readyAbsent (same ▸ List.mem_map_of_mem laterRemaining)
        have unread := firstReadyScalarComputationStep_ready pending pending remaining ready selected
          later laterPending distinct
        simp [unread] at reads
      · rename_i _
        obtain ⟨stuck, closed, within⟩ := ih remaining
          (by
            have := selectedPerm.length_eq
            simp at this
            omega)
          (List.nodup_cons.mp uniqueSelected).2 forward
        exact ⟨stuck, closed, fun step member =>
          selectedPerm.mem_iff.mp (List.mem_cons_of_mem ready (within step member))⟩

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
    ∃ stuck, ScalarComputationStepsReadClosed stuck ∧ ∀ member ∈ stuck, member ∈ steps := by
  unfold certifyScalarComputationPlan at refused
  split at refused
  · rename_i cause certified
    have forwardCause : cause = .forwardDependency step reads := by
      cases cause <;> simp_all [ScalarComputationRunPlanError.inPlan]
    subst forwardCause
    obtain ⟨noDuplicate, forward⟩ :=
      certifyScalarComputationRunWithSteps_forwardDependency _ step reads certified
    have orderPerm := scalarComputationAuthoredOrder_perm steps.length steps
    have unique : (steps.map (·.targetField)).Nodup :=
      (orderPerm.map _).nodup_iff.mp ((fieldId_firstDuplicate_none_iff_nodup _).mp noDuplicate)
    exact scalarComputationAuthoredOrder_forward_readClosed steps.length steps
      (Nat.le_refl _) unique (by
        unfold scalarComputationAuthoredExecutionSteps at forward
        rw [forward]
        simp)
  · simp at refused

/-- A certified run holds no read-closed steps: each step reads no target of a later one. -/
theorem scalarComputationRun_not_readClosed :
    ∀ (steps stuck : List (CheckedScalarComputationStep model)),
      firstForwardScalarComputationDependency? steps = none →
      ScalarComputationStepsReadClosed stuck →
        ¬ ∀ member ∈ stuck, member ∈ steps := by
  intro steps
  induction steps with
  | nil =>
    intro stuck _ closed within
    obtain ⟨step, member⟩ := List.exists_mem_of_ne_nil _ closed.1
    simpa using within step member
  | cons head tail ih =>
    intro stuck ordered closed within
    unfold firstForwardScalarComputationDependency? firstForwardComputationDependency? at ordered
    split at ordered
    · simp at ordered
    · rename_i unread
      have tailOrdered : firstForwardScalarComputationDependency? tail = none := ordered
      by_cases headStuck : head ∈ stuck
      · obtain ⟨other, otherStuck, distinct, reads⟩ := closed.2 head headStuck
        have otherTail : other ∈ tail := by
          rcases List.mem_cons.mp (within other otherStuck) with same | member
          · exact absurd (same ▸ rfl) distinct
          · exact member
        have := List.find?_eq_none.mp unread other otherTail
        simp [reads] at this
      · apply ih stuck tailOrdered closed
        intro member memberStuck
        rcases List.mem_cons.mp (within member memberStuck) with same | inTail
        · exact absurd (same ▸ memberStuck) headStuck
        · exact inTail

/-- A certified plan's authored steps hold no read-closed steps, so every cyclic plan is refused. -/
theorem scalarComputationPlan_not_readClosed
    (plan : CheckedScalarComputationPlan model)
    (stuck : List (CheckedScalarComputationStep model))
    (closed : ScalarComputationStepsReadClosed stuck) :
    ¬ ∀ member ∈ stuck, member ∈ plan.authored := fun within =>
  scalarComputationRun_not_readClosed plan.execution.steps stuck
    plan.execution.dependenciesOrdered closed fun member memberStuck =>
      (scalarComputationPlan_executionSteps_perm plan).mem_iff.mpr (within member memberStuck)

/-- Two authored steps with distinct targets, where the first reads the second's target and the
second does not read the first's, run producer first: the two-step case of the plan order. -/
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
