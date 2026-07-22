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

/-! ## Checked one-star laws -/

@[simp] theorem numericStar_selectedRows_length (rows : List RowIndex) :
    (CheckedNumericStarAggregate.selectedRows rows).length = rows.length := by
  induction rows with
  | nil => rfl
  | cons row rest ih =>
      simp [CheckedNumericStarAggregate.selectedRows, ReopenedStarRows.length, ih]

@[simp] theorem numericStar_selectedRows_closed (rows : List RowIndex) :
    (CheckedNumericStarAggregate.selectedRows rows).hasOpenTail = false := by
  induction rows with
  | nil => rfl
  | cons row rest ih =>
      simp [CheckedNumericStarAggregate.selectedRows, ReopenedStarRows.hasOpenTail, ih,
        ReopenedStarDomain.hasOpenTail]

/-- The checked one-level star reports an omitted source exactly while the instantiated prefix is shorter than the model-owned capacity. -/
theorem checkedNumericStarAggregate_tail_iff
    (checked : CheckedNumericStarAggregate model) (raw : RawSingleGroupContext) :
    (checked.resolvedValueSide raw).hasUninstantiatedTail =
      (raw.candidates.length < checked.repeatability) := by
  simp [CheckedNumericStarAggregate.resolvedValueSide,
    ReopenedStarDomain.toResolvedSide, ReopenedStarDomain.hasOpenTail]

/-- Successful checked Sum evaluation is exactly the established one-declaration aggregate evaluator over the checked resolved side. -/
theorem checkedNumericStarAggregate_evaluateSum_of_valid
    (checked : CheckedNumericStarAggregate model) (raw : RawSingleGroupContext)
    (valid : checked.validateContext raw = .ok ()) :
    checked.evaluateSum raw =
      .ok (evalNumericSumAggregate checked.field.info.signed
        (checked.resolvedValueSide raw)) := by
  unfold CheckedNumericStarAggregate.evaluateSum
  rw [valid]
  rfl

/-- Successful checked extremum evaluation is exactly the established evaluator over the same checked resolved side. -/
theorem checkedNumericStarAggregate_evaluateExtremum_of_valid
    (checked : CheckedNumericStarAggregate model) (op : NumericExtremumOp)
    (raw : RawSingleGroupContext) (valid : checked.validateContext raw = .ok ()) :
    checked.evaluateExtremum op raw =
      .ok (evalNumericExtremumAggregate op (checked.resolvedValueSide raw)) := by
  unfold CheckedNumericStarAggregate.evaluateExtremum
  rw [valid]
  rfl

end A12Kernel
