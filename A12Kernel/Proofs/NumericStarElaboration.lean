import A12Kernel.Elaboration.NumericStar

/-! # Checked finite one-level Number-star construction laws -/

namespace A12Kernel

@[simp] theorem numericStar_selectedRows_length (rows : List RowIndex) :
    (CheckedNumericStarSource.selectedRows rows).length = rows.length := by
  induction rows with
  | nil => rfl
  | cons row rest ih =>
      simp [CheckedNumericStarSource.selectedRows, ReopenedStarRows.length, ih]

@[simp] theorem numericStar_selectedRows_closed (rows : List RowIndex) :
    (CheckedNumericStarSource.selectedRows rows).hasOpenTail = false := by
  induction rows with
  | nil => rfl
  | cons row rest ih =>
      simp [CheckedNumericStarSource.selectedRows, ReopenedStarRows.hasOpenTail, ih,
        ReopenedStarDomain.hasOpenTail]

/-- The checked one-level star reports an omitted source exactly while the instantiated prefix is shorter than the model-owned capacity. -/
theorem checkedNumericStarSource_tail_iff
    (checked : CheckedNumericStarSource model) (raw : RawSingleGroupContext) :
    (checked.resolvedValueSide raw).hasUninstantiatedTail =
      (raw.candidates.length < checked.repeatability) := by
  simp [CheckedNumericStarSource.resolvedValueSide,
    ReopenedStarDomain.toResolvedSide, ReopenedStarDomain.hasOpenTail]

end A12Kernel
