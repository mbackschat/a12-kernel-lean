import A12Kernel.Elaboration.DateTimeDayShiftEvaluation

/-! # Checked elapsed-sub-day then calendar-day DateTime shifts

This bounded composition evaluates one field-backed or dynamic-`Now` `AddHours`,
`AddMinutes`, or `AddSeconds` before one `AddDays`. The exact inner instant and decoded
label feed the existing calendar-day application directly. No wall label is
reconstructed, the dynamic route keeps `World` explicit, and the two operation-specific
structural fault domains remain explicit.

The reverse operation order, wider recursion, differences, targets, and repeatable
placement remain separate.
-/

namespace A12Kernel

/-- Structural failure from the exact operation that was executing. -/
inductive DateTimeSubdayThenDayShiftFault where
  | subday (error : ValueAsDateTimeExtractionFault)
  | day (error : DateTimeDayShiftFault)
  deriving Repr, DecidableEq

namespace CheckedShiftedDateTimeSource

/-- Reuse this checked source and profile with one calendar-day amount. -/
def toCheckedDateTimeDayShift
    (checked : CheckedShiftedDateTimeSource model)
    (amount : CheckedTemporalShiftAmount model) :
    CheckedDateTimeDayShift model := {
  source := checked.source
  sourceAdmitted := checked.sourceAdmitted
  profile := checked.profile
  profileMatches := checked.profileMatches
  amount
}

/-- Evaluate elapsed sub-day arithmetic before one calendar-day mutation, preserving
    the inner exact instant, omission provenance, and generated cause order. -/
def evaluateThenDays (checked : CheckedShiftedDateTimeSource model)
    (nextAmount : CheckedTemporalShiftAmount model)
    (phase : Phase) (input : CheckedDocument model) :
    Except DateTimeSubdayThenDayShiftFault ValueAsDateTimeResult := do
  let source ← checked.evaluate phase input |>.mapError .subday
  (checked.toCheckedDateTimeDayShift nextAmount).evaluateResult
    source phase input |>.mapError .day

end CheckedShiftedDateTimeSource

namespace CheckedShiftedNowDateTimeSource

/-- Evaluate a dynamic elapsed sub-day shift before one calendar-day mutation. The
    supplied `World` is sampled only by the inner operation; the outer landing consumes
    that exact result under the same certified profile. -/
def evaluateThenDays (checked : CheckedShiftedNowDateTimeSource model)
    (nextAmount : CheckedTemporalShiftAmount model)
    (phase : Phase) (world : World) (input : CheckedDocument model) :
    Except DateTimeSubdayThenDayShiftFault ValueAsDateTimeResult := do
  let source ← checked.evaluate phase world input |>.mapError .subday
  CheckedDateTimeDayShift.evaluateProfileResult
    checked.profile nextAmount source phase input |>.mapError .day

end CheckedShiftedNowDateTimeSource

end A12Kernel
