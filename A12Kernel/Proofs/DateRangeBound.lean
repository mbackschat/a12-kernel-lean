import A12Kernel.Elaboration.DateRangeBound

/-! # Checked direct DateRange bound laws -/

namespace A12Kernel

@[simp] theorem dateRangeValue_select_start (value : DateRangeValue) :
    value.select .start = value.start := by
  rfl

@[simp] theorem dateRangeValue_select_finish (value : DateRangeValue) :
    value.select .finish = value.finish := by
  rfl

/-- A reached whole DateRange retains its exact or fragment identity through the shared direct read. -/
theorem directDateRange_evaluate_value
    (operation : CheckedDirectDateRange model) (phase : Phase)
    (input : CheckedDocument model) (cell : CheckedCell)
    (range : DateRangeCellValue)
    (read : input.read { field := operation.source.id, path := [] } = .ok cell)
    (observed : observeCell phase cell = .value (.dateRange range)) :
    operation.evaluate phase input = .ok (.value range) := by
  unfold CheckedDirectDateRange.evaluate
  rw [read]
  simp only [Except.mapError, bind, Except.bind]
  rw [observed]
  rfl

/-- A reached DateRange value transports the selected exact endpoint through the checked read. -/
theorem dateRangeBound_evaluate_value
    (operation : CheckedDateRangeBound model) (phase : Phase)
    (input : CheckedDocument model) (cell : CheckedCell)
    (range : DateRangeValue)
    (read : input.read { field := operation.source.id, path := [] } = .ok cell)
    (observed : observeCell phase cell = .value (.dateRange (.exact range))) :
    operation.evaluate phase input = .ok (.value (range.select operation.bound)) := by
  unfold CheckedDateRangeBound.evaluate
  rw [directDateRange_evaluate_value operation.toCheckedDirectDateRange
    phase input cell (.exact range) read observed]
  rfl

/-- An empty source remains empty rather than acquiring an endpoint or cause. -/
theorem dateRangeBound_evaluate_empty
    (operation : CheckedDateRangeBound model) (phase : Phase)
    (input : CheckedDocument model) (cell : CheckedCell)
    (read : input.read { field := operation.source.id, path := [] } = .ok cell)
    (observed : observeCell phase cell = .empty) :
    operation.evaluate phase input = .ok .empty := by
  unfold CheckedDateRangeBound.evaluate CheckedDirectDateRange.evaluate
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
  unfold CheckedDateRangeBound.evaluate CheckedDirectDateRange.evaluate
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
  unfold CheckedDateRangeBound.evaluate CheckedDirectDateRange.evaluate
  rw [read]
  simp only [Except.mapError, bind, Except.bind]
  rw [observed]
  rfl

/-- A present endpoint is projected once to `FullDate`, while the exact selected value remains in the result. -/
theorem dateRangeBoundComparison_evaluateSelected_value
    (operation : CheckedDateRangeBoundComparison model)
    (value : DateValue) (date : FullDate)
    (resolved : value.toFullDate? = some date) :
    operation.evaluateSelected (.value value) = .ok {
      selected := .value value
      verdict := match operation.position with
        | .left => operation.comparison.evalObserved
            (.value date) (.value operation.expected)
        | .right => operation.comparison.evalObserved
            (.value operation.expected) (.value date)
    } := by
  cases position : operation.position <;>
    simp [CheckedDateRangeBoundComparison.evaluateSelected,
      CheckedDateRangeBoundComparison.projectSelected, resolved,
      position, bind, Except.bind]

/-- Empty selection remains visible and makes either authored comparison position not fire. -/
@[simp] theorem dateRangeBoundComparison_evaluateSelected_empty
    (operation : CheckedDateRangeBoundComparison model) :
    operation.evaluateSelected .empty = .ok {
      selected := .empty
      verdict := .notFired
    } := by
  cases position : operation.position <;>
    simp [CheckedDateRangeBoundComparison.evaluateSelected, position,
      CheckedDateRangeBoundComparison.projectSelected,
      CellObservation.asValidationSimpleOperand, bind, Except.bind,
      TemporalComparisonOp.evalObserved, TemporalComparisonOp.eval,
      evalSymmetricComparison]

/-- Formal unavailability remains visible and makes either authored comparison position unknown. -/
@[simp] theorem dateRangeBoundComparison_evaluateSelected_unknown
    (operation : CheckedDateRangeBoundComparison model)
    (cause : FormalCause) :
    operation.evaluateSelected (.unknown cause) = .ok {
      selected := .unknown cause
      verdict := .unknown
    } := by
  cases position : operation.position <;>
    simp [CheckedDateRangeBoundComparison.evaluateSelected, position,
      CheckedDateRangeBoundComparison.projectSelected,
      CellObservation.asValidationSimpleOperand, bind, Except.bind,
      TemporalComparisonOp.evalObserved, TemporalComparisonOp.eval,
      evalSymmetricComparison]

/-- A present exact endpoint remains available while its selected decoded component becomes fixed. -/
@[simp] theorem dateRangeBoundComponent_evaluateSelected_value
    (operation : CheckedDateRangeBoundComponent model)
    (value : DateValue) :
    operation.evaluateSelected (.value value) = {
      selected := .value value
      component := .value (operation.part.extract value.parts) .fixed
    } := by
  rfl

/-- Empty selection remains visible and delegates to the Date extractor's symmetric fillable zero. -/
@[simp] theorem dateRangeBoundComponent_evaluateSelected_empty
    (operation : CheckedDateRangeBoundComponent model) :
    operation.evaluateSelected .empty = {
      selected := .empty
      component := .value 0 .both
    } := by
  rfl

/-- Formal unavailability remains visible and preserves its exact cause in the numeric operand. -/
@[simp] theorem dateRangeBoundComponent_evaluateSelected_unknown
    (operation : CheckedDateRangeBoundComponent model)
    (cause : FormalCause) :
    operation.evaluateSelected (.unknown cause) = {
      selected := .unknown cause
      component := .unknown cause
    } := by
  rfl


/-- Comparability with a complete date and direct-bound support are the same condition on a
DateRange declaration: both hold exactly when the declaration carries a year of its own or the
model supplies one. The endpoint-versus-fixed-Date consumer therefore gates with the ordinary
temporal admission rule and still reuses the exact bound certificate, without a second policy
precondition that could drift from it. -/
theorem dateRangeInputFormat_supportsDirectBound_eq_comparableWithFullDate
    (format : DateRangeInputFormat) (baseYear : Option Int)
    (comparison : TemporalComparisonOp) :
    format.supportsDirectBound baseYear =
      comparison.admitsFormats baseYear.isSome format.components
        TemporalComponents.fullDate := by
  cases comparison <;> cases format <;>
    cases baseYear <;>
    simp [DateRangeInputFormat.supportsDirectBound,
      TemporalComparisonOp.admitsFormats, DateRangeInputFormat.components,
      TemporalComponents.withBaseYear, TemporalComponents.hasDate,
      TemporalComponents.hasTime, TemporalComponents.fullDate,
      TemporalComparisonOp.requiresSameTimePresence]

end A12Kernel
