import A12Kernel.Elaboration.DateTimeDayShiftComputation
import A12Kernel.Elaboration.DateTimeDayThenSubdayShiftEvaluation
import A12Kernel.Elaboration.DateTimeSubdayThenDayShiftEvaluation

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

/-- One checked dynamic day-then-sub-day shift and declaration-owned target. -/
structure CheckedNowDateTimeDayThenSubdayShiftComputation (model : FlatModel) where
  shift : CheckedNowDateTimeDayShift model
  nextUnit : DateTimeSubdayUnit
  nextAmount : CheckedTemporalShiftAmount model
  target : CheckedDateTimeTarget model

/-- One checked field-backed sub-day-then-day shift and its distinct target. -/
structure CheckedDateTimeSubdayThenDayShiftComputation (model : FlatModel) where
  shift : CheckedShiftedDateTimeSource model
  nextAmount : CheckedTemporalShiftAmount model
  target : CheckedDateTimeTarget model
  sourceDistinct : shift.source.id ≠ target.checked.target.id

/-- One checked dynamic sub-day-then-day shift and declaration-owned target. -/
structure CheckedNowDateTimeSubdayThenDayShiftComputation (model : FlatModel) where
  shift : CheckedShiftedNowDateTimeSource model
  nextAmount : CheckedTemporalShiftAmount model
  target : CheckedDateTimeTarget model

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

/-- Check one dynamic mixed shift and target without sampling the execution world. -/
def elaborateNowDateTimeDayThenSubdayShiftComputation
    (model : FlatModel) (dayAmount : CheckedTemporalShiftAmount model)
    (nextUnit : DateTimeSubdayUnit)
    (nextAmount : CheckedTemporalShiftAmount model)
    (targetField : FieldId) :
    Except DateTimeDayShiftComputationElabError
      (CheckedNowDateTimeDayThenSubdayShiftComputation model) := do
  let shift ←
    elaborateNowDateTimeDayShift model dayAmount |>.mapError .shift
  let target ← elaborateDateTimeTarget model targetField |>.mapError .target
  pure { shift, nextUnit, nextAmount, target }

/-- Check one bounded reverse-order mixed shift and complete-DateTime target. -/
def elaborateDateTimeSubdayThenDayShiftComputation
    (model : FlatModel) (sourceField : FieldId)
    (unit : DateTimeSubdayUnit)
    (subdayAmount nextAmount : CheckedTemporalShiftAmount model)
    (targetField : FieldId) :
    Except DateTimeDayShiftComputationElabError
      (CheckedDateTimeSubdayThenDayShiftComputation model) := do
  let shift ← elaborateShiftedDateTimeSource
    model sourceField unit subdayAmount |>.mapError .shift
  let target ← elaborateDateTimeTarget model targetField |>.mapError .target
  if distinct : shift.source.id = target.checked.target.id then
    throw (.targetSelfReference targetField)
  else
    pure { shift, nextAmount, target, sourceDistinct := distinct }

/-- Check one dynamic reverse-order mixed shift without sampling its world. -/
def elaborateNowDateTimeSubdayThenDayShiftComputation
    (model : FlatModel) (unit : DateTimeSubdayUnit)
    (subdayAmount nextAmount : CheckedTemporalShiftAmount model)
    (targetField : FieldId) :
    Except DateTimeDayShiftComputationElabError
      (CheckedNowDateTimeSubdayThenDayShiftComputation model) := do
  let shift ← elaborateShiftedNowDateTimeSource model unit subdayAmount
    |>.mapError .shift
  let target ← elaborateDateTimeTarget model targetField |>.mapError .target
  pure { shift, nextAmount, target }

/-- Structural execution failure outside the rich DateTime target outcome. -/
inductive DateTimeMixedShiftComputationFault where
  | shift (error : DateTimeDayThenSubdayShiftFault)
  | target (error : DateTimeTargetEvaluationFault)
  deriving Repr, DecidableEq

/-- Structural failure from a reverse-order mixed shift or its target. -/
inductive DateTimeReverseMixedShiftComputationFault where
  | shift (error : DateTimeSubdayThenDayShiftFault)
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

namespace CheckedNowDateTimeDayThenSubdayShiftComputation

/-- Execute both operations from this call's world and retain the final instant. -/
def evaluateOperand (operation :
    CheckedNowDateTimeDayThenSubdayShiftComputation model)
    (world : World) (input : CheckedDocument model) :
    Except DateTimeMixedShiftComputationFault TemporalComputationResult :=
  match operation.shift.evaluateThenSubday operation.nextUnit
      operation.nextAmount .computation world input with
  | .error error => .error (.shift error)
  | .ok result => .ok result.asTemporalComputationResult

/-- Execute the dynamic mixed shift through declaration-owned rendering. -/
def evaluateOutcome (operation :
    CheckedNowDateTimeDayThenSubdayShiftComputation model)
    (world : World) (input : CheckedDocument model) :
    Except DateTimeMixedShiftComputationFault DateTimeTargetOutcome :=
  match operation.evaluateOperand world input with
  | .error error => .error error
  | .ok result => operation.target.evaluate result |>.mapError .target

/-- Classify the rich dynamic outcome against the immutable source document. -/
def executeResult (operation :
    CheckedNowDateTimeDayThenSubdayShiftComputation model)
    (world : World) (input : CheckedDocument model)
    (residualMessages : List ResidualMessage) :
    Except DateTimeMixedShiftComputationFault
      (DateTimeComputationRunView ResidualMessage) := do
  let outcome ← operation.evaluateOutcome world input
  pure (DateTimeComputationRunView.fromOutcomes input residualMessages
    [(operation.target.checked.target.id, outcome)])

end CheckedNowDateTimeDayThenSubdayShiftComputation

namespace CheckedDateTimeSubdayThenDayShiftComputation

/-- Execute elapsed arithmetic before calendar mutation and retain the final instant. -/
def evaluateOperand (operation :
    CheckedDateTimeSubdayThenDayShiftComputation model)
    (input : CheckedDocument model) :
    Except DateTimeReverseMixedShiftComputationFault
      TemporalComputationResult :=
  match operation.shift.evaluateThenDays
      operation.nextAmount .computation input with
  | .error error => .error (.shift error)
  | .ok result => .ok result.asTemporalComputationResult

/-- Execute the reverse-order result through declaration-owned rendering. -/
def evaluateOutcome (operation :
    CheckedDateTimeSubdayThenDayShiftComputation model)
    (input : CheckedDocument model) :
    Except DateTimeReverseMixedShiftComputationFault DateTimeTargetOutcome :=
  match operation.evaluateOperand input with
  | .error error => .error error
  | .ok result => operation.target.evaluate result |>.mapError .target

/-- Classify the rich outcome against the immutable source document. -/
def executeResult (operation :
    CheckedDateTimeSubdayThenDayShiftComputation model)
    (input : CheckedDocument model) (residualMessages : List ResidualMessage) :
    Except DateTimeReverseMixedShiftComputationFault
      (DateTimeComputationRunView ResidualMessage) := do
  let outcome ← operation.evaluateOutcome input
  pure (DateTimeComputationRunView.fromOutcomes input residualMessages
    [(operation.target.checked.target.id, outcome)])

end CheckedDateTimeSubdayThenDayShiftComputation

namespace CheckedNowDateTimeSubdayThenDayShiftComputation

/-- Execute elapsed arithmetic from this world before calendar mutation. -/
def evaluateOperand (operation :
    CheckedNowDateTimeSubdayThenDayShiftComputation model)
    (world : World) (input : CheckedDocument model) :
    Except DateTimeReverseMixedShiftComputationFault
      TemporalComputationResult :=
  match operation.shift.evaluateThenDays
      operation.nextAmount .computation world input with
  | .error error => .error (.shift error)
  | .ok result => .ok result.asTemporalComputationResult

/-- Execute the dynamic reverse result through declaration-owned rendering. -/
def evaluateOutcome (operation :
    CheckedNowDateTimeSubdayThenDayShiftComputation model)
    (world : World) (input : CheckedDocument model) :
    Except DateTimeReverseMixedShiftComputationFault DateTimeTargetOutcome :=
  match operation.evaluateOperand world input with
  | .error error => .error error
  | .ok result => operation.target.evaluate result |>.mapError .target

/-- Classify the rich dynamic result against the immutable source document. -/
def executeResult (operation :
    CheckedNowDateTimeSubdayThenDayShiftComputation model)
    (world : World) (input : CheckedDocument model)
    (residualMessages : List ResidualMessage) :
    Except DateTimeReverseMixedShiftComputationFault
      (DateTimeComputationRunView ResidualMessage) := do
  let outcome ← operation.evaluateOutcome world input
  pure (DateTimeComputationRunView.fromOutcomes input residualMessages
    [(operation.target.checked.target.id, outcome)])

end CheckedNowDateTimeSubdayThenDayShiftComputation

end A12Kernel
