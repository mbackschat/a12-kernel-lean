import A12Kernel.Elaboration.NumericAggregate

/-! # Checked nonrepeatable Number Sum lowering laws -/

namespace A12Kernel

/-- This checked subset never invents an uninstantiated source. -/
theorem checkedNumericSum_noUninstantiated
    (sum : CheckedNumericSum model) (raw : RawFlatContext) :
    (sum.resolvedSide raw).uninstantiatedSignedness = [] := by
  rfl

/-- This checked subset never invents a `Having` marker. -/
theorem checkedNumericSum_noHaving
    (sum : CheckedNumericSum model) (raw : RawFlatContext) :
    (sum.resolvedSide raw).hasHaving = false := by
  rfl

/-- Checked evaluation is exactly the established resolved per-declaration evaluator. -/
theorem checkedNumericSum_evaluate
    (sum : CheckedNumericSum model) (raw : RawFlatContext) :
    sum.evaluate raw = evalDeclaredNumericSumAggregate (sum.resolvedSide raw) := by
  rfl

end A12Kernel
