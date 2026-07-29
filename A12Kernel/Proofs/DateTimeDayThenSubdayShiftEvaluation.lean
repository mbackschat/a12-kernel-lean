import A12Kernel.Elaboration.DateTimeDayThenSubdayShiftEvaluation

/-! # Calendar-day then elapsed-sub-day DateTime laws -/

namespace A12Kernel

/-- A reached formal cause from the inner calendar-day shift decides the composition
    before the outer elapsed amount is read. -/
theorem checkedDateTimeDayShift_evaluateThenSubday_inner_unavailable
    (checked : CheckedDateTimeDayShift model)
    (nextUnit : DateTimeSubdayUnit)
    (nextAmount : CheckedTemporalShiftAmount model)
    (phase : Phase) (input : CheckedDocument model)
    (cause : FormalCause)
    (inner :
      CheckedDateTimeDayShift.evaluate checked phase input =
        .ok (.unavailable cause)) :
    CheckedDateTimeDayShift.evaluateThenSubday checked
        nextUnit nextAmount phase input =
      .ok (.unavailable cause) := by
  simp [CheckedDateTimeDayShift.evaluateThenSubday, inner,
    ValueAsDateTimeResult.evaluateShiftedAmount, Except.mapError,
    bind, Except.bind]

/-- A cause-free inner calendar-day no-value still reaches a formal outer elapsed
    amount. -/
theorem checkedDateTimeDayShift_evaluateThenSubday_noValue_reaches_amount
    (checked : CheckedDateTimeDayShift model)
    (nextUnit : DateTimeSubdayUnit)
    (nextAmount : CheckedTemporalShiftAmount model)
    (phase : Phase) (input : CheckedDocument model)
    (notGiven : Bool) (cause : FormalCause)
    (inner :
      CheckedDateTimeDayShift.evaluate checked phase input =
        .ok (.noValue notGiven))
    (outer :
      nextAmount.read phase input = .ok (.error (.formal cause))) :
    CheckedDateTimeDayShift.evaluateThenSubday checked
        nextUnit nextAmount phase input =
      .ok (.unavailable cause) := by
  simp [CheckedDateTimeDayShift.evaluateThenSubday, inner,
    ValueAsDateTimeResult.evaluateShiftedAmount, outer,
    Except.mapError, bind, Except.bind]

/-- A reached formal cause from the dynamic calendar-day shift decides composition
    before the outer elapsed amount is read. -/
theorem checkedNowDateTimeDayShift_evaluateThenSubday_inner_unavailable
    (checked : CheckedNowDateTimeDayShift model)
    (nextUnit : DateTimeSubdayUnit)
    (nextAmount : CheckedTemporalShiftAmount model)
    (phase : Phase) (world : World) (input : CheckedDocument model)
    (cause : FormalCause)
    (inner :
      checked.evaluate phase world input = .ok (.unavailable cause)) :
    checked.evaluateThenSubday nextUnit nextAmount phase world input =
      .ok (.unavailable cause) := by
  simp [CheckedNowDateTimeDayShift.evaluateThenSubday, inner,
    ValueAsDateTimeResult.evaluateShiftedAmount, Except.mapError,
    bind, Except.bind]

/-- A cause-free dynamic calendar-day no-value still reaches a formal outer elapsed
    amount. -/
theorem checkedNowDateTimeDayShift_evaluateThenSubday_noValue_reaches_amount
    (checked : CheckedNowDateTimeDayShift model)
    (nextUnit : DateTimeSubdayUnit)
    (nextAmount : CheckedTemporalShiftAmount model)
    (phase : Phase) (world : World) (input : CheckedDocument model)
    (notGiven : Bool) (cause : FormalCause)
    (inner :
      checked.evaluate phase world input = .ok (.noValue notGiven))
    (outer :
      nextAmount.read phase input = .ok (.error (.formal cause))) :
    checked.evaluateThenSubday nextUnit nextAmount phase world input =
      .ok (.unavailable cause) := by
  simp [CheckedNowDateTimeDayShift.evaluateThenSubday, inner,
    ValueAsDateTimeResult.evaluateShiftedAmount, outer,
    Except.mapError, bind, Except.bind]

end A12Kernel
