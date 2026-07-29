import A12Kernel.Elaboration.DateTimeSubdayThenDayShiftEvaluation

/-! # Elapsed-sub-day then calendar-day DateTime laws -/

namespace A12Kernel

/-- A reached formal cause from the inner elapsed shift decides the composition before
    the outer calendar-day amount is read. -/
theorem checkedShiftedDateTimeSource_evaluateThenDays_inner_unavailable
    (checked : CheckedShiftedDateTimeSource model)
    (nextAmount : CheckedTemporalShiftAmount model)
    (phase : Phase) (input : CheckedDocument model)
    (cause : FormalCause)
    (inner :
      checked.evaluate phase input = .ok (.unavailable cause)) :
    checked.evaluateThenDays nextAmount phase input =
      .ok (.unavailable cause) := by
  simp [CheckedShiftedDateTimeSource.evaluateThenDays, inner,
    CheckedDateTimeDayShift.evaluateResult, Except.mapError,
    bind, Except.bind]

/-- A cause-free inner elapsed no-value still reaches a formal outer calendar-day
    amount. -/
theorem checkedShiftedDateTimeSource_evaluateThenDays_noValue_reaches_amount
    (checked : CheckedShiftedDateTimeSource model)
    (nextAmount : CheckedTemporalShiftAmount model)
    (phase : Phase) (input : CheckedDocument model)
    (notGiven : Bool) (cause : FormalCause)
    (inner : checked.evaluate phase input = .ok (.noValue notGiven))
    (outer :
      nextAmount.read phase input = .ok (.error (.formal cause))) :
    checked.evaluateThenDays nextAmount phase input =
      .ok (.unavailable cause) := by
  simp [CheckedShiftedDateTimeSource.evaluateThenDays, inner,
    CheckedShiftedDateTimeSource.toCheckedDateTimeDayShift,
    CheckedDateTimeDayShift.evaluateResult, outer, Except.mapError,
    bind, Except.bind]

end A12Kernel
