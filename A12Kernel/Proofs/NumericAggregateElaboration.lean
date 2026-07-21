import A12Kernel.Elaboration.NumericAggregate

/-! # Checked nonrepeatable Number aggregate lowering laws -/

namespace A12Kernel

/-- Both resolved views classify the same explicit cells in the same order. -/
theorem checkedNumericAggregate_sameCells
    (checked : CheckedNumericAggregateFields model) (raw : RawFlatContext) :
    (checked.resolvedSumSide raw).valueCells =
      (checked.resolvedValueSide raw).cells := by
  simp [CheckedNumericAggregateFields.resolvedSumSide,
    CheckedNumericAggregateFields.resolvedValueSide,
    ResolvedNumericSumSide.valueCells]

/-- This checked subset never invents an uninstantiated extremum source. -/
theorem checkedNumericAggregate_noUninstantiatedTail
    (checked : CheckedNumericAggregateFields model) (raw : RawFlatContext) :
    (checked.resolvedValueSide raw).hasUninstantiatedTail = false := by
  rfl

/-- This checked subset never invents an uninstantiated Sum source. -/
theorem checkedNumericAggregate_noUninstantiatedSumSource
    (checked : CheckedNumericAggregateFields model) (raw : RawFlatContext) :
    (checked.resolvedSumSide raw).uninstantiatedSignedness = [] := by
  rfl

/-- Neither resolved view invents a `Having` marker. -/
theorem checkedNumericAggregate_noHaving
    (checked : CheckedNumericAggregateFields model) (raw : RawFlatContext) :
    (checked.resolvedValueSide raw).hasHaving = false ∧
      (checked.resolvedSumSide raw).hasHaving = false := by
  exact ⟨rfl, rfl⟩

/-- Checked Sum evaluation is exactly the established resolved per-declaration evaluator. -/
theorem checkedNumericAggregate_evaluateSum
    (checked : CheckedNumericAggregateFields model) (raw : RawFlatContext) :
    checked.evaluateSum raw =
      evalDeclaredNumericSumAggregate (checked.resolvedSumSide raw) := by
  rfl

/-- Checked extremum evaluation is exactly the established resolved evaluator. -/
theorem checkedNumericAggregate_evaluateExtremum
    (checked : CheckedNumericAggregateFields model) (op : NumericExtremumOp)
    (raw : RawFlatContext) :
    checked.evaluateExtremum op raw =
      evalNumericExtremumAggregate op (checked.resolvedValueSide raw) := by
  rfl

end A12Kernel
