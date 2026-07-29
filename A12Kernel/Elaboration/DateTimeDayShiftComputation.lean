import A12Kernel.Elaboration.DateTimeComputationApplication
import A12Kernel.Elaboration.DateTimeDayShiftEvaluation

/-! # Checked DateTime day-shift computations

This capsule executes one direct nonrepeatable `AddDays(DateTime, Number)` through one
distinct declaration-owned DateTime target, then delegates the rich outcome to the
existing public result view and application path. The shift retains its exact instant
until target rendering; target text and source-relative change remain owned by the
settled DateTime target/result capsules.

Alternatives, scheduling, repeatable placement, wider recursive expressions, generated
validation, and message construction remain separate. The existing `Now` computation
carrier is not widened.
-/

namespace A12Kernel

/-- Static refusal before one checked DateTime day shift can target a declaration. -/
inductive DateTimeDayShiftComputationElabError where
  | shift (error : ValueAsDateTimeExtractionElabError)
  | target (error : DateTimeTargetElabError)
  | targetSelfReference (field : FieldId)
  deriving Repr, DecidableEq

/-- One checked direct DateTime day shift and its distinct declaration-owned target. -/
structure CheckedDateTimeDayShiftComputation (model : FlatModel) where
  shift : CheckedDateTimeDayShift model
  target : CheckedDateTimeTarget model
  sourceDistinct :
    shift.source.id ≠ target.checked.target.id

/-- Check one direct DateTime day shift and one distinct complete-DateTime target. -/
def elaborateDateTimeDayShiftComputation
    (model : FlatModel) (sourceField : FieldId)
    (amount : CheckedTemporalShiftAmount model) (targetField : FieldId) :
    Except DateTimeDayShiftComputationElabError
      (CheckedDateTimeDayShiftComputation model) := do
  let shift ←
    elaborateDateTimeDayShift model sourceField amount |>.mapError .shift
  let target ← elaborateDateTimeTarget model targetField |>.mapError .target
  if distinct : shift.source.id = target.checked.target.id then
    throw (.targetSelfReference targetField)
  else
    pure { shift, target, sourceDistinct := distinct }

/-- Structural execution failure outside the rich DateTime target outcome. -/
inductive DateTimeDayShiftComputationFault where
  | shift (error : DateTimeDayShiftFault)
  | target (error : DateTimeTargetEvaluationFault)
  deriving Repr, DecidableEq

namespace ValueAsDateTimeResult

/-- Project one generated DateTime expression result into target execution. Quiet
    no-value and cause-free non-relevance store nothing; a reached formal cause remains
    poison; a value carries only its exact instant into declaration-owned rendering. -/
def asTemporalComputationResult :
    ValueAsDateTimeResult → TemporalComputationResult
  | .noValue _ | .nonRelevant => .noValue
  | .value _ instant _ => .value instant
  | .unavailable cause => .poison cause

end ValueAsDateTimeResult

namespace CheckedDateTimeDayShiftComputation

/-- Execute the checked shift in computation phase and retain its target-facing result. -/
def evaluateOperand (operation : CheckedDateTimeDayShiftComputation model)
    (input : CheckedDocument model) :
    Except DateTimeDayShiftComputationFault TemporalComputationResult :=
  match operation.shift.evaluate .computation input with
  | .error error => .error (.shift error)
  | .ok result => .ok result.asTemporalComputationResult

/-- Execute the checked shift through the existing declaration-owned DateTime target. -/
def evaluateOutcome (operation : CheckedDateTimeDayShiftComputation model)
    (input : CheckedDocument model) :
    Except DateTimeDayShiftComputationFault DateTimeTargetOutcome :=
  match operation.evaluateOperand input with
  | .error error => .error error
  | .ok result => operation.target.evaluate result |>.mapError .target

/-- Execute and classify the one rich target outcome against the immutable source
    document. Residual messages remain already-classified opaque input. -/
def executeResult (operation : CheckedDateTimeDayShiftComputation model)
    (input : CheckedDocument model)
    (residualMessages : List ResidualMessage) :
    Except DateTimeDayShiftComputationFault
      (DateTimeComputationRunView ResidualMessage) := do
  let outcome ← operation.evaluateOutcome input
  pure (DateTimeComputationRunView.fromOutcomes input residualMessages
    [(operation.target.checked.target.id, outcome)])

end CheckedDateTimeDayShiftComputation

end A12Kernel
