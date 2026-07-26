import A12Kernel.Elaboration.ParallelNumericAlternativeTable
import A12Kernel.Proofs.ParallelNumericDirectRun

/-! # Parallel Number alternative-table laws -/

namespace A12Kernel

theorem checkedParallelNumericAlternativeTable_wellFormed
    (table : CheckedParallelNumericAlternativeTable model) :
    table.WellFormed := by
  intro alternative member
  exact ⟨checkedIsolatedParallelNumericDirectRun_wellFormed
      alternative.operation,
    alternative.preconditionOwned, alternative.targetMatches⟩

theorem parallelNumericAlternativeTable_noMatch
    (table : CheckedParallelNumericAlternativeTable model)
    (context : ScalarComputationContext)
    (selection : ComputationAlternative.selectFirst
      table.selectableAlternatives context = .noMatch) :
    table.evaluate context = .ok .noValue := by
  simp [CheckedParallelNumericAlternativeTable.evaluate, selection]

theorem parallelNumericAlternativeTable_guardPoison
    (table : CheckedParallelNumericAlternativeTable model)
    (context : ScalarComputationContext) (cause : FormalCause)
    (selection : ComputationAlternative.selectFirst
      table.selectableAlternatives context = .poison cause) :
    table.evaluate context = .ok (.inheritedPoison cause) := by
  simp [CheckedParallelNumericAlternativeTable.evaluate, selection]

theorem parallelNumericAlternativeTable_selected
    (table : CheckedParallelNumericAlternativeTable model)
    (context : ScalarComputationContext)
    (operation : CheckedIsolatedParallelNumericDirectRun model)
    (selection : ComputationAlternative.selectFirst
      table.selectableAlternatives context = .selected operation) :
    table.evaluate context = operation.evaluateSelected context := by
  simp [CheckedParallelNumericAlternativeTable.evaluate, selection]

end A12Kernel
