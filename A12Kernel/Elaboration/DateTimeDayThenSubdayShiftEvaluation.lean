import A12Kernel.Elaboration.DateTimeDayShiftEvaluation

/-! # Checked calendar-day then elapsed-sub-day DateTime shifts

This bounded composition evaluates one field-backed or dynamic-`Now` `AddDays` before
one `AddHours`, `AddMinutes`, or `AddSeconds`. The exact calendar landing feeds elapsed
arithmetic directly, so operation order, overlap identity, milliseconds, omission
provenance, and explicit world transport remain observable.

Wider recursion, differences, targets, and repeatable placement remain separate.
-/

namespace A12Kernel

/-- Structural failure from the exact operation that was executing. -/
inductive DateTimeDayThenSubdayShiftFault where
  | day (error : DateTimeDayShiftFault)
  | subday (error : ValueAsDateTimeExtractionFault)
  deriving Repr, DecidableEq

namespace CheckedDateTimeDayShift

/-- Evaluate one calendar-day mutation before one elapsed sub-day shift, preserving
    the calendar landing's exact instant and generated cause order. -/
def evaluateThenSubday (checked : CheckedDateTimeDayShift model)
    (nextUnit : DateTimeSubdayUnit)
    (nextAmount : CheckedTemporalShiftAmount model)
    (phase : Phase) (input : CheckedDocument model) :
    Except DateTimeDayThenSubdayShiftFault ValueAsDateTimeResult := do
  let source ←
    CheckedDateTimeDayShift.evaluate checked phase input |>.mapError .day
  source.evaluateShiftedAmount checked.profile
    nextUnit nextAmount phase input |>.mapError .subday

end CheckedDateTimeDayShift

namespace CheckedNowDateTimeDayShift

/-- Evaluate one dynamic calendar-day mutation before one elapsed sub-day shift. The
    supplied `World` remains the sole dynamic input and the outer operation consumes
    the exact calendar landing. -/
def evaluateThenSubday (checked : CheckedNowDateTimeDayShift model)
    (nextUnit : DateTimeSubdayUnit)
    (nextAmount : CheckedTemporalShiftAmount model)
    (phase : Phase) (world : World) (input : CheckedDocument model) :
    Except DateTimeDayThenSubdayShiftFault ValueAsDateTimeResult := do
  let source ← checked.evaluate phase world input |>.mapError .day
  source.evaluateShiftedAmount checked.profile
    nextUnit nextAmount phase input |>.mapError .subday

end CheckedNowDateTimeDayShift

end A12Kernel
