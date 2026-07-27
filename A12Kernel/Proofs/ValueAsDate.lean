import A12Kernel.Elaboration.ValueAsDateDayDifference
import A12Kernel.Elaboration.ValueAsDateShiftTarget
import A12Kernel.Elaboration.ValueAsDateTimeField

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

/-- A reached source or amount poison crosses the composed shift/target boundary unchanged; target rendering and basic checks are not run. -/
theorem valueAsDateShiftTarget_evaluate_poison
    (checked : CheckedValueAsDateShiftTarget model)
    (cell : CheckedCell
      (AdmittedPartiallyKnownDate checked.shift.source.policy.partialMode))
    (amount : NumericComputationResult) (cause : FormalCause)
    (shifted : checked.shift.evaluate cell amount = .ok (.poison cause)) :
    checked.evaluateOutcome cell amount = .ok (.poison cause) := by
  rw [CheckedValueAsDateShiftTarget.evaluateOutcome, shifted]
  rfl

/-- The composed entry classifies the checked target's exact rich outcome through the established immutable full-Date result owner; it does not rebuild source placement or reclassify the target. -/
theorem valueAsDateShiftTarget_executeResult_projects
    (checked : CheckedValueAsDateShiftTarget model)
    (input : CheckedDocument model) (raw : RawCell String)
    (amount : NumericComputationResult)
    (residualMessages : List ResidualMessage)
    (outcome : FullDateTargetOutcome)
    (evaluated : checked.evaluateRaw raw amount = .ok outcome) :
    checked.executeResult input raw amount residualMessages =
      .ok (FullDateComputationRunView.fromOutcomes input residualMessages
        [(checked.target.checked.target.id, outcome)]) := by
  rw [CheckedValueAsDateShiftTarget.executeResult, evaluated]
  rfl

/-- Cause-free non-relevance projects to UNKNOWN only at the enclosing validation boundary. -/
@[simp] theorem valueAsDateDifference_evalFixedRight_nonRelevant
    (op : NumericComparisonOp) (expected : Rat) :
    ValueAsDateDifferenceResult.nonRelevant.evalFixedRight op expected =
      .unknown := by
  rfl

/-- When the partial Date is authored first, its formal cause wins before the ordinary operand can contribute its cause. -/
theorem valueAsDateDifference_evaluate_left_unavailable
    (checked : CheckedValueAsDateDifference model)
    (phase : Phase)
    (cell : CheckedCell
      (AdmittedPartiallyKnownDate checked.source.policy.partialMode))
    (sourceCause otherCause : FormalCause)
    (placement : checked.placement = .left)
    (observed :
      checked.toCheckedValueAsDateSource.observe phase cell =
        .unavailable sourceCause) :
    checked.evaluate phase cell (.unavailable otherCause) =
      .ok (.operand (.unknown sourceCause)) := by
  rw [CheckedValueAsDateDifference.evaluate.eq_def, placement, observed]
  rfl

/-- When the ordinary Date is authored first, its formal cause wins before the partial-Date read can contribute its cause. -/
theorem valueAsDateDifference_evaluate_right_unavailable
    (checked : CheckedValueAsDateDifference model)
    (phase : Phase)
    (cell : CheckedCell
      (AdmittedPartiallyKnownDate checked.source.policy.partialMode))
    (otherCause : FormalCause)
    (placement : checked.placement = .right)
    :
    checked.evaluate phase cell (.unavailable otherCause) =
      .ok (.operand (.unknown otherCause)) := by
  rw [CheckedValueAsDateDifference.evaluate.eq_def, placement]
  rfl

/-- Date-side formal unavailability stops construction before the direct Time observation can contribute another cause. -/
theorem valueAsDateTime_evaluate_date_unavailable
    (checked : CheckedValueAsDateTime model)
    (phase : Phase)
    (cell : CheckedCell
      (AdmittedPartiallyKnownDate checked.source.policy.partialMode))
    (time : CellObservation TimeOfDay)
    (cause : FormalCause)
    (observed :
      checked.toCheckedValueAsDateSource.observe phase cell =
        .unavailable cause) :
    checked.evaluate phase cell time = .unavailable cause := by
  rw [CheckedValueAsDateTime.evaluate.eq_def, observed]

/-- Generated left-to-right argument evaluation does not read the checked Time field after the partial-Date source has already failed formally. -/
theorem valueAsDateTimeField_evaluateRaw_date_unavailable
    (checked : CheckedValueAsDateTimeField model)
    (phase : Phase) (input : CheckedDocument model)
    (raw : RawCell String) (cause : FormalCause)
    (observed :
      checked.construction.toCheckedValueAsDateSource.observe phase
        (checked.construction.toCheckedValueAsDateSource.checkSourceRaw raw) =
          .unavailable cause) :
    checked.evaluateRaw phase input raw = .ok (.unavailable cause) := by
  rw [CheckedValueAsDateTimeField.evaluateRaw, observed]
  rfl

/-- A cause-free unknown year dominates an ordinary empty Time only after the Time read has completed without a formal cause. -/
theorem valueAsDateTime_evaluate_nonRelevant_empty
    (checked : CheckedValueAsDateTime model)
    (phase : Phase)
    (cell : CheckedCell
      (AdmittedPartiallyKnownDate checked.source.policy.partialMode))
    (observed :
      checked.toCheckedValueAsDateSource.observe phase cell =
        .nonRelevant) :
    checked.evaluate phase cell .empty = .nonRelevant := by
  rw [CheckedValueAsDateTime.evaluate.eq_def, observed]

/-- Construction non-relevance reaches UNKNOWN only at the exact-instant validation consumer. -/
@[simp] theorem valueAsDateTime_evalFixedRight_nonRelevant
    (op : TemporalComparisonOp) (expected : Instant) :
    ValueAsDateTimeResult.nonRelevant.evalFixedRight op expected =
      .unknown := by
  rfl

/-- A left-positioned partial-Date formal cause wins before the ordinary calendar-day operand is inspected. -/
theorem valueAsDateDayDifference_evaluate_left_unavailable
    (checked : CheckedValueAsDateDayDifference model)
    (phase : Phase)
    (cell : CheckedCell
      (AdmittedPartiallyKnownDate checked.source.policy.partialMode))
    (other : CalendarDayDifferenceOperand)
    (cause : FormalCause)
    (placement : checked.placement = .left)
    (observed :
      checked.toCheckedZonedValueAsDateSource.toCheckedValueAsDateSource.observe
        phase cell = .unavailable cause) :
    checked.evaluate phase cell other =
      .ok (.operand (.unknown cause)) := by
  rw [CheckedValueAsDateDayDifference.evaluate.eq_def, placement, observed]
  rfl

/-- A right-positioned ordinary formal cause wins without consulting the partial-Date observation. -/
theorem valueAsDateDayDifference_evaluate_right_unavailable
    (checked : CheckedValueAsDateDayDifference model)
    (phase : Phase)
    (cell : CheckedCell
      (AdmittedPartiallyKnownDate checked.source.policy.partialMode))
    (cause : FormalCause)
    (placement : checked.placement = .right) :
    checked.evaluate phase cell (.unavailable cause) =
      .ok (.operand (.unknown cause)) := by
  rw [CheckedValueAsDateDayDifference.evaluate.eq_def, placement]
  rfl

/-- Unknown-year non-relevance remains distinct from the ordinary day-difference empty-zero path. -/
theorem valueAsDateDayDifference_evaluate_nonRelevant_empty
    (checked : CheckedValueAsDateDayDifference model)
    (phase : Phase)
    (cell : CheckedCell
      (AdmittedPartiallyKnownDate checked.source.policy.partialMode))
    (observed :
      checked.toCheckedZonedValueAsDateSource.toCheckedValueAsDateSource.observe
        phase cell = .nonRelevant) :
    checked.evaluate phase cell .empty = .ok .nonRelevant := by
  rw [CheckedValueAsDateDayDifference.evaluate.eq_def, observed]
  cases checked.placement <;> rfl

end A12Kernel
