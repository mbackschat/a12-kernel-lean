import A12Kernel.Elaboration.ValueAsDate

namespace A12Kernel

/-- Endpoint choice is observationally irrelevant for a fully known stored Date. -/
@[simp] theorem partiallyKnownDateValue_resolve_full
    (date : FullDate) (endpoint : ValueAsDateEndpoint) :
    (PartiallyKnownDateValue.full date).resolve endpoint = .date date := by
  cases endpoint <;> rfl

/-- A present typed source resolves its endpoint and then uses the established full-Date comparison without a second verdict rule. -/
theorem valueAsDate_evaluate_value
    (checked : CheckedValueAsDateComparison model)
    (cell : CheckedCell
      (AdmittedPartiallyKnownDate checked.source.policy.partialMode))
    (source : AdmittedPartiallyKnownDate checked.source.policy.partialMode)
    (resolved : FullDate)
    (observed : observeCell .validation cell = .value source) :
    (resolution : source.resolve checked.endpoint = .date resolved) →
    checked.evaluate cell =
      checked.comparison.eval
        (.value resolved true) (.value checked.expected true) := by
  intro resolution
  simp [CheckedValueAsDateComparison.evaluate, TemporalComparisonOp.evalObserved,
    observed, CellObservation.resolvePartiallyKnownDate, resolution,
    CellObservation.asValidationSimpleOperand]

/-- A physically absent or present-empty source preserves the direct-Date comparison's not-evaluated result. -/
theorem valueAsDate_evaluate_empty
    (checked : CheckedValueAsDateComparison model)
    (cell : CheckedCell
      (AdmittedPartiallyKnownDate checked.source.policy.partialMode))
    (observed : observeCell .validation cell = .empty) :
    checked.evaluate cell = .notFired := by
  simp [CheckedValueAsDateComparison.evaluate, TemporalComparisonOp.evalObserved,
    observed, CellObservation.resolvePartiallyKnownDate,
    CellObservation.asValidationSimpleOperand,
    TemporalComparisonOp.eval, evalSymmetricComparison]

/-- An admitted unknown-year source becomes non-relevant at the operation boundary and therefore cannot fire a comparison. -/
theorem valueAsDate_evaluate_nonRelevant
    (checked : CheckedValueAsDateComparison model)
    (cell : CheckedCell
      (AdmittedPartiallyKnownDate checked.source.policy.partialMode))
    (source : AdmittedPartiallyKnownDate checked.source.policy.partialMode)
    (observed : observeCell .validation cell = .value source)
    (resolution : source.resolve checked.endpoint = .nonRelevant) :
    checked.evaluate cell = .notFired := by
  simp [CheckedValueAsDateComparison.evaluate, TemporalComparisonOp.evalObserved,
    observed, CellObservation.resolvePartiallyKnownDate, resolution,
    CellObservation.asValidationSimpleOperand, TemporalComparisonOp.eval,
    evalSymmetricComparison]

/-- Formal source invalidity is never completed to an endpoint; it retains the existing UNKNOWN verdict. -/
theorem valueAsDate_evaluate_unknown
    (checked : CheckedValueAsDateComparison model)
    (cell : CheckedCell
      (AdmittedPartiallyKnownDate checked.source.policy.partialMode))
    (cause : FormalCause)
    (observed : observeCell .validation cell = .unknown cause) :
    checked.evaluate cell = .unknown := by
  simp [CheckedValueAsDateComparison.evaluate, TemporalComparisonOp.evalObserved,
    observed, CellObservation.resolvePartiallyKnownDate,
    CellObservation.asValidationSimpleOperand,
    TemporalComparisonOp.eval, evalSymmetricComparison]

end A12Kernel
