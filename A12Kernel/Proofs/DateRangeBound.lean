import A12Kernel.Elaboration.DateRangeBound

/-! # Checked direct DateRange bound laws -/

namespace A12Kernel

@[simp] theorem dateRangeValue_select_start (value : DateRangeValue) :
    value.select .start = value.start := by
  rfl

@[simp] theorem dateRangeValue_select_finish (value : DateRangeValue) :
    value.select .finish = value.finish := by
  rfl

/-- A reached DateRange value transports the selected exact endpoint through the checked read. -/
theorem dateRangeBound_evaluate_value
    (operation : CheckedDateRangeBound model) (phase : Phase)
    (input : CheckedDocument model) (cell : CheckedCell)
    (range : DateRangeValue)
    (read : input.read { field := operation.source.id, path := [] } = .ok cell)
    (observed : observeCell phase cell = .value (.dateRange range)) :
    operation.evaluate phase input = .ok (.value (range.select operation.bound)) := by
  unfold CheckedDateRangeBound.evaluate
  rw [read]
  simp only [Except.mapError, bind, Except.bind]
  rw [observed]
  rfl

/-- An empty source remains empty rather than acquiring an endpoint or cause. -/
theorem dateRangeBound_evaluate_empty
    (operation : CheckedDateRangeBound model) (phase : Phase)
    (input : CheckedDocument model) (cell : CheckedCell)
    (read : input.read { field := operation.source.id, path := [] } = .ok cell)
    (observed : observeCell phase cell = .empty) :
    operation.evaluate phase input = .ok .empty := by
  unfold CheckedDateRangeBound.evaluate
  rw [read]
  simp only [Except.mapError, bind, Except.bind]
  rw [observed]
  rfl

/-- Validation unavailability keeps its exact cause and does not select an endpoint. -/
theorem dateRangeBound_evaluate_unknown
    (operation : CheckedDateRangeBound model) (phase : Phase)
    (input : CheckedDocument model) (cell : CheckedCell) (cause : FormalCause)
    (read : input.read { field := operation.source.id, path := [] } = .ok cell)
    (observed : observeCell phase cell = .unknown cause) :
    operation.evaluate phase input = .ok (.unknown cause) := by
  unfold CheckedDateRangeBound.evaluate
  rw [read]
  simp only [Except.mapError, bind, Except.bind]
  rw [observed]
  rfl

/-- Computation unavailability keeps its exact poison cause and does not select an endpoint. -/
theorem dateRangeBound_evaluate_poison
    (operation : CheckedDateRangeBound model) (phase : Phase)
    (input : CheckedDocument model) (cell : CheckedCell) (cause : FormalCause)
    (read : input.read { field := operation.source.id, path := [] } = .ok cell)
    (observed : observeCell phase cell = .poison cause) :
    operation.evaluate phase input = .ok (.poison cause) := by
  unfold CheckedDateRangeBound.evaluate
  rw [read]
  simp only [Except.mapError, bind, Except.bind]
  rw [observed]
  rfl

end A12Kernel
