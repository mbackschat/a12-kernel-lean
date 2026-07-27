import A12Kernel.Elaboration.ValueAsDate

namespace A12Kernel

/-- Endpoint choice is observationally irrelevant for a fully known stored Date. -/
@[simp] theorem dayOptionalDate_resolve_full
    (date : FullDate) (endpoint : ValueAsDateEndpoint) :
    (DayOptionalDate.full date).resolve endpoint = date := by
  cases endpoint <;> rfl

/-- A present typed source resolves its endpoint and then uses the established full-Date comparison without a second verdict rule. -/
theorem valueAsDate_evaluate_value
    (checked : CheckedValueAsDateComparison model)
    (cell : CheckedCell DayOptionalDate) (source : DayOptionalDate)
    (observed : observeCell .validation cell = .value source) :
    checked.evaluate cell =
      checked.comparison.eval
        (.value (source.resolve checked.endpoint) true)
        (.value checked.expected true) := by
  simp [CheckedValueAsDateComparison.evaluate, TemporalComparisonOp.evalObserved,
    observed, CellObservation.resolveDayOptional,
    CellObservation.asValidationSimpleOperand]

/-- A physically absent or present-empty source preserves the direct-Date comparison's not-evaluated result. -/
theorem valueAsDate_evaluate_empty
    (checked : CheckedValueAsDateComparison model)
    (cell : CheckedCell DayOptionalDate)
    (observed : observeCell .validation cell = .empty) :
    checked.evaluate cell = .notFired := by
  simp [CheckedValueAsDateComparison.evaluate, TemporalComparisonOp.evalObserved,
    observed, CellObservation.resolveDayOptional, CellObservation.asValidationSimpleOperand,
    TemporalComparisonOp.eval, evalSymmetricComparison]

/-- Formal source invalidity is never completed to an endpoint; it retains the existing UNKNOWN verdict. -/
theorem valueAsDate_evaluate_unknown
    (checked : CheckedValueAsDateComparison model)
    (cell : CheckedCell DayOptionalDate) (cause : FormalCause)
    (observed : observeCell .validation cell = .unknown cause) :
    checked.evaluate cell = .unknown := by
  simp [CheckedValueAsDateComparison.evaluate, TemporalComparisonOp.evalObserved,
    observed, CellObservation.resolveDayOptional, CellObservation.asValidationSimpleOperand,
    TemporalComparisonOp.eval, evalSymmetricComparison]

end A12Kernel
