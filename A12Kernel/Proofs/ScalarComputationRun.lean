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
    (target : field ∈ run.targetFields)
    (found : state.find? field = some completion) :
    (run.stringContext state input).read field =
      completion.stringCell := by
  simp [CheckedScalarComputationRun.stringContext, target, found]

theorem scalarComputationRun_stringRead_input
    (run : CheckedScalarComputationRun model)
    (state : ScalarComputationRunState)
    (input : CheckedDocument model)
    (field : FieldId)
    (ordinary : field ∉ run.targetFields) :
    (run.stringContext state input).read field =
      input.stringComputationContext.read field := by
  simp [CheckedScalarComputationRun.stringContext, ordinary]

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
    (target : field ∈ run.targetFields)
    (found : state.find? field = some completion) :
    (run.numberContext world state input).read field =
      completion.numberCell := by
  simp [CheckedScalarComputationRun.numberContext, target, found]

theorem scalarComputationRun_numberRead_input
    (run : CheckedScalarComputationRun model)
    (world : World)
    (state : ScalarComputationRunState)
    (input : CheckedDocument model)
    (field : FieldId)
    (ordinary : field ∉ run.targetFields) :
    (run.numberContext world state input).read field =
      input.flatContext.read field := by
  simp [CheckedScalarComputationRun.numberContext,
    CheckedDocument.scalarComputationContext, ordinary]

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

end A12Kernel
