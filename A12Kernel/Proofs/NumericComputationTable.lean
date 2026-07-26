import A12Kernel.Elaboration.NumericComputation.Table

/-! # Checked Number computation-table laws -/

namespace A12Kernel

/-- Clean exhaustion projects to the Number target's clean no-value outcome. -/
theorem numericComputationTable_noMatch
    (table : CheckedNumericComputationTable model)
    (context : ScalarComputationContext)
    (selection : ComputationAlternative.selectFirst
      table.selectableAlternatives context = .noMatch) :
    table.evaluate context = .ok (.supported .noValue) := by
  simp [CheckedNumericComputationTable.evaluate, selection]
  rfl

/-- A guard poison ends selection and becomes inherited target poison without evaluating a row. -/
theorem numericComputationTable_guardPoison
    (table : CheckedNumericComputationTable model)
    (context : ScalarComputationContext) (cause : FormalCause)
    (selection : ComputationAlternative.selectFirst
      table.selectableAlternatives context = .poison cause) :
    table.evaluate context = .ok (.supported (.inheritedPoison cause)) := by
  simp [CheckedNumericComputationTable.evaluate, selection]
  rfl

/-- A selected checked operation is the sole operation evaluated by the table. -/
theorem numericComputationTable_selected
    (table : CheckedNumericComputationTable model)
    (context : ScalarComputationContext)
    (operation : CheckedNumericTargetComputationOperation model)
    (selection : ComputationAlternative.selectFirst
      table.selectableAlternatives context = .selected operation) :
    table.evaluate context = operation.evaluate context := by
  simp [CheckedNumericComputationTable.evaluate, selection]

end A12Kernel
