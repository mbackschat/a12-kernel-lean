import A12Kernel.Elaboration.DateTimeDayShiftEvaluation

/-! # Checked DateTime day-shift differences

This capsule combines one checked `AddDays(DateTime, Number)` result with one direct
DateTime in `DifferenceInDays`, in either authored operand position. The shift retains
its exact instant and omission provenance; the direct operand reuses the same checked
complete-DateTime/profile certificate. The existing concrete-profile calendar-day core
owns the count.

Other recursive forms, Date operands, other zones, repeatable placement, and numeric
target storage remain outside.
-/

namespace A12Kernel

/-- Structural failure in one bounded DateTime shift/difference composition. -/
inductive DateTimeDayShiftDifferenceFault where
  | shift (error : DateTimeDayShiftFault)
  | document (error : CheckedDocumentError)
  | operationUnavailable (position : ShiftDifferencePosition)
  deriving Repr, DecidableEq

/-- One checked DateTime day shift combined with one direct DateTime in authored order. -/
structure CheckedDateTimeDayShiftDifference (model : FlatModel) where
  shift : CheckedDateTimeDayShift model
  other : CheckedDateTimeSource model
  position : ShiftDifferencePosition

/-- Check one direct DateTime day shift and its other direct DateTime difference operand. -/
def elaborateDateTimeDayShiftDifference
    (model : FlatModel) (sourceField : FieldId)
    (amount : CheckedTemporalShiftAmount model)
    (otherField : FieldId) (position : ShiftDifferencePosition) :
    Except ValueAsDateTimeExtractionElabError
      (CheckedDateTimeDayShiftDifference model) := do
  let shift ← elaborateDateTimeDayShift model sourceField amount
  let other ← elaborateDateTimeSource model otherField
  pure { shift, other, position }

namespace ValueAsDateTimeResult

/-- Project an exact DateTime shift result into the existing calendar-day operand.
    Cause-free non-relevance is outside this direct source route and remains a
    structural unsupported-calendar state if a forged result reaches it. -/
def calendarDayDifferenceOperand :
    ValueAsDateTimeResult → CalendarDayDifferenceOperand
  | .noValue _ => .empty
  | .value localDateTime instant _ => .value localDateTime instant
  | .nonRelevant => .unsupportedCalendar
  | .unavailable cause => .unavailable cause

/-- Omission carried by a value-producing or value-less DateTime shift. -/
def shiftNotGiven : ValueAsDateTimeResult → Bool
  | .noValue notGiven | .value _ _ notGiven => notGiven
  | .nonRelevant | .unavailable _ => false

end ValueAsDateTimeResult

namespace CheckedDateTimeSource

/-- Read one direct checked DateTime as the other calendar-day operand. -/
def readCalendarDayOperand (checked : CheckedDateTimeSource model)
    (phase : Phase) (input : CheckedDocument model) :
    Except CheckedDocumentError CalendarDayDifferenceOperand := do
  let cell ← input.read { field := checked.source.id, path := [] }
  pure (CalendarDayDifferenceOperand.ofObservation (observeCell phase cell))

end CheckedDateTimeSource

namespace CheckedDateTimeDayShiftDifference

private def finish
    (checked : CheckedDateTimeDayShiftDifference model)
    (shiftResult : ValueAsDateTimeResult)
    (other : CalendarDayDifferenceOperand) :
    Except DateTimeDayShiftDifferenceFault NumericOperand :=
  let shiftOperand := shiftResult.calendarDayDifferenceOperand
  let evaluated :=
    match checked.position with
    | .first =>
        CalendarDayDifferenceOperand.evaluate
          checked.shift.profile shiftOperand other
    | .second =>
        CalendarDayDifferenceOperand.evaluate
          checked.shift.profile other shiftOperand
  match evaluated with
  | .error () => .error (.operationUnavailable checked.position)
  | .ok (.unknown cause) => .ok (.unknown cause)
  | .ok (.value amount fillability) =>
      .ok (.value amount
        (if shiftResult.shiftNotGiven then .both else fillability))

/-- Evaluate the shift and direct DateTime in authored order. The first reached formal
    cause stops before the later operand, while empty/no-value still reaches it. -/
def evaluate (checked : CheckedDateTimeDayShiftDifference model)
    (phase : Phase) (input : CheckedDocument model) :
    Except DateTimeDayShiftDifferenceFault NumericOperand :=
  match checked.position with
  | .first =>
      match checked.shift.evaluate phase input with
      | .error error => .error (.shift error)
      | .ok (.unavailable cause) => .ok (.unknown cause)
      | .ok shiftResult =>
          match checked.other.readCalendarDayOperand phase input with
          | .error error => .error (.document error)
          | .ok (.unavailable cause) => .ok (.unknown cause)
          | .ok other => checked.finish shiftResult other
  | .second =>
      match checked.other.readCalendarDayOperand phase input with
      | .error error => .error (.document error)
      | .ok (.unavailable cause) => .ok (.unknown cause)
      | .ok other =>
          match checked.shift.evaluate phase input with
          | .error error => .error (.shift error)
          | .ok (.unavailable cause) => .ok (.unknown cause)
          | .ok shiftResult => checked.finish shiftResult other

end CheckedDateTimeDayShiftDifference

end A12Kernel
