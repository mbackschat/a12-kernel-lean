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
  simp [CheckedValueAsDateComparison.evaluate,
    CheckedValueAsDateComparison.observe,
    CheckedValueAsDateSource.observe, observed,
    CellObservation.resolvePartiallyKnownDate, resolution]

/-- A physically absent or present-empty source preserves the direct-Date comparison's not-evaluated result. -/
theorem valueAsDate_evaluate_empty
    (checked : CheckedValueAsDateComparison model)
    (cell : CheckedCell
      (AdmittedPartiallyKnownDate checked.source.policy.partialMode))
    (observed : observeCell .validation cell = .empty) :
    checked.evaluate cell = .notFired := by
  simp [CheckedValueAsDateComparison.evaluate,
    CheckedValueAsDateComparison.observe,
    CheckedValueAsDateSource.observe, observed,
    CellObservation.resolvePartiallyKnownDate]

/-- An admitted unknown-year source becomes non-relevant at the operation boundary and therefore makes an enclosing comparison UNKNOWN rather than merely absent. -/
theorem valueAsDate_evaluate_nonRelevant
    (checked : CheckedValueAsDateComparison model)
    (cell : CheckedCell
      (AdmittedPartiallyKnownDate checked.source.policy.partialMode))
    (source : AdmittedPartiallyKnownDate checked.source.policy.partialMode)
    (observed : observeCell .validation cell = .value source)
    (resolution : source.resolve checked.endpoint = .nonRelevant) :
    checked.evaluate cell = .unknown := by
  simp [CheckedValueAsDateComparison.evaluate,
    CheckedValueAsDateComparison.observe,
    CheckedValueAsDateSource.observe, observed,
    CellObservation.resolvePartiallyKnownDate, resolution]

/-- Formal source invalidity is never completed to an endpoint; it retains the existing UNKNOWN verdict. -/
theorem valueAsDate_evaluate_unknown
    (checked : CheckedValueAsDateComparison model)
    (cell : CheckedCell
      (AdmittedPartiallyKnownDate checked.source.policy.partialMode))
    (cause : FormalCause)
    (observed : observeCell .validation cell = .unknown cause) :
    checked.evaluate cell = .unknown := by
  simp [CheckedValueAsDateComparison.evaluate,
    CheckedValueAsDateComparison.observe,
    CheckedValueAsDateSource.observe, observed,
    CellObservation.resolvePartiallyKnownDate]

/-- Physical absence remains non-evaluated through the exact stored-text adapter. -/
@[simp] theorem valueAsDate_evaluateRaw_empty
    (checked : CheckedValueAsDateComparison model) :
    checked.evaluateRaw .empty = .notFired := by
  simp [CheckedValueAsDateComparison.evaluateRaw,
    CheckedValueAsDateComparison.checkSourceRaw,
    CheckedValueAsDateSource.checkSourceRaw, checkRawCellWith,
    CheckedValueAsDateComparison.evaluate,
    CheckedValueAsDateComparison.observe,
    CheckedValueAsDateSource.observe, observeCell,
    CellObservation.resolvePartiallyKnownDate]

/-- A preceding parser rejection keeps its exact formal cause and suppresses endpoint evaluation. -/
@[simp] theorem valueAsDate_evaluateRaw_rejected
    (checked : CheckedValueAsDateComparison model)
    (cause : BaseFormalCause) :
    checked.evaluateRaw (.rejected cause) = .unknown := by
  simp [CheckedValueAsDateComparison.evaluateRaw,
    CheckedValueAsDateComparison.checkSourceRaw,
    CheckedValueAsDateSource.checkSourceRaw, checkRawCellWith,
    CheckedValueAsDateComparison.evaluate,
    CheckedValueAsDateComparison.observe,
    CheckedValueAsDateSource.observe, observeCell,
    CellObservation.resolvePartiallyKnownDate]

/-- A reached poison in the right numeric operand still dominates an empty left value because generated argument evaluation reaches it before the calendar helper. -/
theorem valueAsDateShift_evaluate_empty_amountPoison
    (checked : CheckedValueAsDateShift model)
    (cell : CheckedCell
      (AdmittedPartiallyKnownDate checked.source.policy.partialMode))
    (cause : FormalCause)
    (observed :
      checked.toCheckedValueAsDateSource.observe Phase.computation cell =
        .empty) :
    checked.evaluate cell (.poison cause) = .ok (.poison cause) := by
  rw [CheckedValueAsDateShift.evaluate.eq_def, observed]
  rfl

end A12Kernel
