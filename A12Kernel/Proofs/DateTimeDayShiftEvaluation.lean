import A12Kernel.Elaboration.DateTimeDayShiftEvaluation
import A12Kernel.Proofs.BerlinLegacyCalendarArithmetic

/-! # Checked DateTime calendar-day shift laws -/

namespace A12Kernel

/-- A reached exact zero amount preserves the already selected DateTime instant under
    both admitted profiles; an ambiguous Berlin label is never re-resolved. -/
@[simp] theorem checkedDateTimeDayShift_applyAmount_zero
    (checked : CheckedDateTimeDayShift model)
    (sourceLocal : LocalDateTime) (sourceInstant : Instant) :
    checked.applyAmount sourceLocal sourceInstant
        (.value 0 .fixed) =
      .ok (.value sourceLocal sourceInstant false) := by
  have offsetZero : temporalShiftAmountToInt32 0 = 0 := by
    decide
  cases profileEq : checked.profile
  all_goals
    simp [CheckedDateTimeDayShift.applyAmount, offsetZero, profileEq,
      CheckedDateTimeDayShift.utcLanding?, NumericFillability.fixed,
      pure, Except.pure]

/-- A reached formal DateTime source decides the generated source-before-amount
    evaluation without any hypothesis about the amount or its document cell. -/
theorem checkedDateTimeDayShift_source_unavailable
    (checked : CheckedDateTimeDayShift model)
    (phase : Phase) (input : CheckedDocument model)
    (cell : CheckedCell) (cause : FormalCause)
    (read :
      input.read { field := checked.source.id, path := [] } = .ok cell)
    (observed : observeCell phase cell = .unknown cause) :
    checked.evaluate phase input = .ok (.unavailable cause) := by
  have cellResult :
      checked.evaluateCell phase input cell =
        .ok (.unavailable cause) := by
    simp [CheckedDateTimeDayShift.evaluateCell, observed,
      pure, Except.pure]
  simp [CheckedDateTimeDayShift.evaluate, read, cellResult,
    Except.mapError, bind, Except.bind]

/-- An empty DateTime source still reaches the amount, whose formal cause remains
    visible instead of being replaced by ordinary source missingness. -/
theorem checkedDateTimeDayShift_empty_reaches_amount
    (checked : CheckedDateTimeDayShift model)
    (phase : Phase) (input : CheckedDocument model)
    (cell : CheckedCell) (cause : FormalCause)
    (read :
      input.read { field := checked.source.id, path := [] } = .ok cell)
    (observed : observeCell phase cell = .empty)
    (amount :
      checked.amount.read phase input =
        .ok (.error (.formal cause))) :
    checked.evaluate phase input = .ok (.unavailable cause) := by
  have cellResult :
      checked.evaluateCell phase input cell =
        .ok (.unavailable cause) := by
    simp [CheckedDateTimeDayShift.evaluateCell, observed, amount,
      Except.mapError, bind, Except.bind, pure, Except.pure]
  simp [CheckedDateTimeDayShift.evaluate, read, cellResult,
    Except.mapError, bind, Except.bind]

/-- A reached inner formal cause decides nested generated evaluation before the outer
    DateTime day amount is read. -/
theorem checkedDateTimeDayShift_evaluateThen_inner_unavailable
    (checked : CheckedDateTimeDayShift model)
    (nextAmount : CheckedTemporalShiftAmount model)
    (phase : Phase) (input : CheckedDocument model)
    (cause : FormalCause)
    (inner :
      checked.evaluate phase input = .ok (.unavailable cause)) :
    checked.evaluateThen nextAmount phase input =
      .ok (.unavailable cause) := by
  simp [CheckedDateTimeDayShift.evaluateThen, inner,
    CheckedDateTimeDayShift.evaluateResult]

end A12Kernel
