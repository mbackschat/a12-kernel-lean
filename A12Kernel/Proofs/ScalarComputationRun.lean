import A12Kernel.Elaboration.ScalarComputationRun

/-! # Finite mixed scalar computation-run laws

These laws expose consumer-specific pending/completed/input reads and prove that atomic evaluation retains the selected table's family rather than lowering to a common outcome.
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

/-- Analyze always sees the exact caller-authored target order. -/
@[simp] theorem scalarComputationPair_authoredTargetFields
    (pair : CheckedScalarComputationPair model) :
    pair.authoredTargetFields =
      [pair.authoredFirst.targetField, pair.authoredSecond.targetField] := by
  rfl

/-- A first-authored consumer of the second target selects producer-first execution. -/
theorem scalarComputationPairExecutionSteps_forward
    (first second : CheckedScalarComputationStep model)
    (forward : first.referencesField second.targetField = true) :
    scalarComputationPairExecutionSteps first second = [second, first] := by
  simp [scalarComputationPairExecutionSteps, forward]

/-- A pair without that forward edge preserves authored execution order. -/
theorem scalarComputationPairExecutionSteps_preserved
    (first second : CheckedScalarComputationStep model)
    (forward : first.referencesField second.targetField = false) :
    scalarComputationPairExecutionSteps first second = [first, second] := by
  simp [scalarComputationPairExecutionSteps, forward]

/-- A checked pair retains the exact selected steps, including their operations rather than only their target identities. -/
@[simp] theorem scalarComputationPair_executionSteps
    (pair : CheckedScalarComputationPair model) :
    pair.execution.steps =
      scalarComputationPairExecutionSteps
        pair.authoredFirst pair.authoredSecond := by
  exact pair.executionUsesSelectedSteps

/-- Pair execution is exactly the established typed mixed-run execution. -/
theorem scalarComputationPair_execute
    (pair : CheckedScalarComputationPair model)
    (world : World)
    (patterns : PreparedFlatStringPatterns model compilePattern)
    (input : CheckedDocument model) :
    pair.execute world patterns input =
      pair.execution.execute world patterns input := by
  rfl

end A12Kernel
