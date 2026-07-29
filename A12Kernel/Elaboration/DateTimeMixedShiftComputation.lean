import A12Kernel.Elaboration.DateTimeDayShiftComputation
import A12Kernel.Elaboration.DateTimeDayThenSubdayShiftEvaluation

/-! # Checked mixed DateTime shift computations

This capsule executes one field-backed calendar-day shift followed by one elapsed sub-day shift through a distinct DateTime target, retaining the inner exact instant.
Dynamic sources, reverse order, recursion, scheduling, and repeatable placement remain
separate.
-/

namespace A12Kernel

/-- One checked field-backed day-then-sub-day shift and its distinct target. -/
structure CheckedDateTimeDayThenSubdayShiftComputation (model : FlatModel) where
  shift : CheckedDateTimeDayShift model
  nextUnit : DateTimeSubdayUnit
  nextAmount : CheckedTemporalShiftAmount model
  target : CheckedDateTimeTarget model
  sourceDistinct : shift.source.id ≠ target.checked.target.id

/-- Check one bounded field-backed mixed shift and complete-DateTime target. -/
def elaborateDateTimeDayThenSubdayShiftComputation
    (model : FlatModel) (sourceField : FieldId)
    (dayAmount : CheckedTemporalShiftAmount model)
    (nextUnit : DateTimeSubdayUnit)
    (nextAmount : CheckedTemporalShiftAmount model)
    (targetField : FieldId) :
    Except DateTimeDayShiftComputationElabError
      (CheckedDateTimeDayThenSubdayShiftComputation model) := do
  let shift ←
    elaborateDateTimeDayShift model sourceField dayAmount |>.mapError .shift
  let target ← elaborateDateTimeTarget model targetField |>.mapError .target
  if distinct : shift.source.id = target.checked.target.id then
    throw (.targetSelfReference targetField)
  else
    pure { shift, nextUnit, nextAmount, target, sourceDistinct := distinct }

/-- Structural execution failure outside the rich DateTime target outcome. -/
inductive DateTimeMixedShiftComputationFault where
  | shift (error : DateTimeDayThenSubdayShiftFault)
  | target (error : DateTimeTargetEvaluationFault)
  deriving Repr, DecidableEq

namespace CheckedDateTimeDayThenSubdayShiftComputation

/-- Execute both operations in computation phase and retain the exact final instant. -/
def evaluateOperand (operation :
    CheckedDateTimeDayThenSubdayShiftComputation model)
    (input : CheckedDocument model) :
    Except DateTimeMixedShiftComputationFault TemporalComputationResult :=
  match operation.shift.evaluateThenSubday operation.nextUnit
      operation.nextAmount .computation input with
  | .error error => .error (.shift error)
  | .ok result => .ok result.asTemporalComputationResult

/-- Execute the mixed shift through declaration-owned DateTime rendering. -/
def evaluateOutcome (operation :
    CheckedDateTimeDayThenSubdayShiftComputation model)
    (input : CheckedDocument model) :
    Except DateTimeMixedShiftComputationFault DateTimeTargetOutcome :=
  match operation.evaluateOperand input with
  | .error error => .error error
  | .ok result => operation.target.evaluate result |>.mapError .target

/-- Classify the rich outcome against the immutable source document. -/
def executeResult (operation :
    CheckedDateTimeDayThenSubdayShiftComputation model)
    (input : CheckedDocument model) (residualMessages : List ResidualMessage) :
    Except DateTimeMixedShiftComputationFault
      (DateTimeComputationRunView ResidualMessage) := do
  let outcome ← operation.evaluateOutcome input
  pure (DateTimeComputationRunView.fromOutcomes input residualMessages
    [(operation.target.checked.target.id, outcome)])

end CheckedDateTimeDayThenSubdayShiftComputation

end A12Kernel
