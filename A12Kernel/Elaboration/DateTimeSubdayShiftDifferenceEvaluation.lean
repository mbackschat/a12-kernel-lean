import A12Kernel.Elaboration.ValueAsDateTimeExtraction
import A12Kernel.Semantics.DateTimeDifference

/-! # Checked DateTime sub-day shift differences

This capsule combines one checked field-backed sub-day shift with one direct DateTime in an elapsed difference, in either authored operand position. Its exact instant enters `DateTimeDifferenceOperand` directly; no label is rendered or resolved again.

Dynamic `Now`, calendar-day differences, wider recursion, targets, scheduling, repeatable placement, and other temporal operands remain separate.
-/

namespace A12Kernel

/-- Structural failure in one bounded sub-day shift/difference composition. -/
inductive DateTimeSubdayShiftDifferenceFault where
  | shift (error : ValueAsDateTimeExtractionFault)
  | document (error : CheckedDocumentError)
  | operationUnavailable (position : ShiftDifferencePosition)
  deriving Repr, DecidableEq

/-- One checked sub-day DateTime shift, direct DateTime, elapsed unit, and authored position. -/
structure CheckedDateTimeSubdayShiftDifference (model : FlatModel) where
  shift : CheckedShiftedDateTimeSource model
  other : CheckedDateTimeSource model
  differenceUnit : DateTimeSubdayUnit
  position : ShiftDifferencePosition

/-- Check one field-backed exact shift and its other direct DateTime difference
    operand. All admitted sources expose the complete DateTime component set. -/
def elaborateDateTimeSubdayShiftDifference
    (model : FlatModel) (sourceField : FieldId)
    (shiftUnit : DateTimeSubdayUnit)
    (amount : CheckedTemporalShiftAmount model)
    (otherField : FieldId) (differenceUnit : DateTimeSubdayUnit)
    (position : ShiftDifferencePosition) :
    Except ValueAsDateTimeExtractionElabError
      (CheckedDateTimeSubdayShiftDifference model) := do
  let shift ←
    elaborateShiftedDateTimeSource model sourceField shiftUnit amount
  let other ← elaborateDateTimeSource model otherField
  pure { shift, other, differenceUnit, position }

namespace ValueAsDateTimeResult

/-- Project one exact shift result into the elapsed-difference operand. Cause-free
    non-relevance is unreachable for the direct source and remains explicit. -/
def dateTimeDifferenceOperand? :
    ValueAsDateTimeResult → Option DateTimeDifferenceOperand
  | .noValue _ => some .empty
  | .value _ instant _ => some (.value instant)
  | .unavailable cause => some (.unavailable cause)
  | .nonRelevant => none

end ValueAsDateTimeResult

namespace CheckedDateTimeSource

/-- Read one direct checked DateTime as an exact elapsed-difference operand. -/
def readDateTimeDifferenceOperand (checked : CheckedDateTimeSource model)
    (phase : Phase) (input : CheckedDocument model) :
    Except CheckedDocumentError DateTimeDifferenceOperand := do
  let cell ← input.read { field := checked.source.id, path := [] }
  pure (DateTimeDifferenceOperand.ofObservation (observeCell phase cell))

end CheckedDateTimeSource

namespace CheckedDateTimeSubdayShiftDifference

private def finish
    (checked : CheckedDateTimeSubdayShiftDifference model)
    (shiftResult : ValueAsDateTimeResult)
    (other : DateTimeDifferenceOperand) :
    Except DateTimeSubdayShiftDifferenceFault NumericOperand := do
  let shiftOperand ←
    match shiftResult.dateTimeDifferenceOperand? with
    | some operand => pure operand
    | none => throw (.operationUnavailable checked.position)
  let evaluated :=
    match checked.position with
    | .first =>
        DateTimeDifferenceOperand.evaluate
          checked.differenceUnit shiftOperand other
    | .second =>
        DateTimeDifferenceOperand.evaluate
          checked.differenceUnit other shiftOperand
  match evaluated with
  | .unknown cause => pure (.unknown cause)
  | .value value fillability =>
      pure (.value value
        (if shiftResult.shiftNotGiven then .both else fillability))

/-- Evaluate the shift and direct DateTime in authored order. The first reached formal
    cause stops before the later operand, while cause-free no-value still reaches it. -/
def evaluate (checked : CheckedDateTimeSubdayShiftDifference model)
    (phase : Phase) (input : CheckedDocument model) :
    Except DateTimeSubdayShiftDifferenceFault NumericOperand :=
  match checked.position with
  | .first =>
      match checked.shift.evaluate phase input with
      | .error error => .error (.shift error)
      | .ok (.unavailable cause) => .ok (.unknown cause)
      | .ok .nonRelevant => .error (.operationUnavailable .first)
      | .ok shiftResult =>
          match checked.other.readDateTimeDifferenceOperand phase input with
          | .error error => .error (.document error)
          | .ok (.unavailable cause) => .ok (.unknown cause)
          | .ok other => checked.finish shiftResult other
  | .second =>
      match checked.other.readDateTimeDifferenceOperand phase input with
      | .error error => .error (.document error)
      | .ok (.unavailable cause) => .ok (.unknown cause)
      | .ok other =>
          match checked.shift.evaluate phase input with
          | .error error => .error (.shift error)
          | .ok (.unavailable cause) => .ok (.unknown cause)
          | .ok .nonRelevant => .error (.operationUnavailable .second)
          | .ok shiftResult => checked.finish shiftResult other

end CheckedDateTimeSubdayShiftDifference

end A12Kernel
