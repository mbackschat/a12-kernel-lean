import A12Kernel.Elaboration.DateTimeComputationApplication
import A12Kernel.Elaboration.DateTimeDayShiftEvaluation

/-! # Checked DateTime day-shift computations

This capsule executes one direct nonrepeatable `AddDays(DateTime, Number)`, dynamic
`AddDays(Now, Number)`, or bounded field-backed/dynamic two-day continuation through
one declaration-owned DateTime target, then delegates the rich outcome to the existing
public result view and application path. Each shift retains its exact instant until
target rendering; target text and source-relative change remain owned by the settled
DateTime target/result capsules.

Alternatives, scheduling, repeatable placement, wider recursive expressions, generated
validation, and message construction remain separate. The field and dynamic carriers
remain distinct because only the field-backed form owns a source declaration and
self-reference obligation. Checked day amounts read only Number declarations, so a
validated model cannot make either amount the DateTime target declaration.
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

/-- One checked dynamic `Now` day shift and its declaration-owned target. -/
structure CheckedNowDateTimeDayShiftComputation (model : FlatModel) where
  shift : CheckedNowDateTimeDayShift model
  target : CheckedDateTimeTarget model

/-- One checked field-backed two-day continuation and its distinct target. -/
structure CheckedDateTimeTwoDayShiftComputation (model : FlatModel) where
  shift : CheckedDateTimeDayShift model
  nextAmount : CheckedTemporalShiftAmount model
  target : CheckedDateTimeTarget model
  sourceDistinct : shift.source.id ≠ target.checked.target.id

/-- One checked dynamic two-day continuation and its declaration-owned target. -/
structure CheckedNowDateTimeTwoDayShiftComputation (model : FlatModel) where
  shift : CheckedNowDateTimeDayShift model
  nextAmount : CheckedTemporalShiftAmount model
  target : CheckedDateTimeTarget model

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

/-- Check one dynamic `Now` day shift and complete-DateTime target without sampling
    the execution world. -/
def elaborateNowDateTimeDayShiftComputation
    (model : FlatModel) (amount : CheckedTemporalShiftAmount model)
    (targetField : FieldId) :
    Except DateTimeDayShiftComputationElabError
      (CheckedNowDateTimeDayShiftComputation model) := do
  let shift ← elaborateNowDateTimeDayShift model amount |>.mapError .shift
  let target ← elaborateDateTimeTarget model targetField |>.mapError .target
  pure { shift, target }

/-- Check one field-backed two-day continuation and distinct complete-DateTime target. -/
def elaborateDateTimeTwoDayShiftComputation
    (model : FlatModel) (sourceField : FieldId)
    (firstAmount nextAmount : CheckedTemporalShiftAmount model)
    (targetField : FieldId) :
    Except DateTimeDayShiftComputationElabError
      (CheckedDateTimeTwoDayShiftComputation model) := do
  let shift ←
    elaborateDateTimeDayShift model sourceField firstAmount |>.mapError .shift
  let target ← elaborateDateTimeTarget model targetField |>.mapError .target
  if distinct : shift.source.id = target.checked.target.id then
    throw (.targetSelfReference targetField)
  else
    pure { shift, nextAmount, target, sourceDistinct := distinct }

/-- Check one dynamic two-day continuation and complete-DateTime target without
    sampling the execution world. -/
def elaborateNowDateTimeTwoDayShiftComputation
    (model : FlatModel)
    (firstAmount nextAmount : CheckedTemporalShiftAmount model)
    (targetField : FieldId) :
    Except DateTimeDayShiftComputationElabError
      (CheckedNowDateTimeTwoDayShiftComputation model) := do
  let shift ←
    elaborateNowDateTimeDayShift model firstAmount |>.mapError .shift
  let target ← elaborateDateTimeTarget model targetField |>.mapError .target
  pure { shift, nextAmount, target }

/-- Structural execution failure outside the rich DateTime target outcome. -/
inductive DateTimeDayShiftComputationFault where
  | shift (error : DateTimeDayShiftFault)
  | target (error : DateTimeTargetEvaluationFault)
  deriving Repr, DecidableEq

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

namespace CheckedNowDateTimeDayShiftComputation

/-- Sample this call's exact world once, then retain the checked day-shift result. -/
def evaluateOperand (operation : CheckedNowDateTimeDayShiftComputation model)
    (world : World) (input : CheckedDocument model) :
    Except DateTimeDayShiftComputationFault TemporalComputationResult :=
  match operation.shift.evaluate .computation world input with
  | .error error => .error (.shift error)
  | .ok result => .ok result.asTemporalComputationResult

/-- Execute the dynamic day shift through declaration-owned DateTime rendering. -/
def evaluateOutcome (operation : CheckedNowDateTimeDayShiftComputation model)
    (world : World) (input : CheckedDocument model) :
    Except DateTimeDayShiftComputationFault DateTimeTargetOutcome :=
  match operation.evaluateOperand world input with
  | .error error => .error error
  | .ok result => operation.target.evaluate result |>.mapError .target

/-- Execute and classify the rich target outcome against the immutable source. -/
def executeResult (operation : CheckedNowDateTimeDayShiftComputation model)
    (world : World) (input : CheckedDocument model)
    (residualMessages : List ResidualMessage) :
    Except DateTimeDayShiftComputationFault
      (DateTimeComputationRunView ResidualMessage) := do
  let outcome ← operation.evaluateOutcome world input
  pure (DateTimeComputationRunView.fromOutcomes input residualMessages
    [(operation.target.checked.target.id, outcome)])

end CheckedNowDateTimeDayShiftComputation

namespace CheckedDateTimeTwoDayShiftComputation

/-- Run both field-backed day amounts and retain the exact target-facing result. -/
def evaluateOperand (operation : CheckedDateTimeTwoDayShiftComputation model)
    (input : CheckedDocument model) :
    Except DateTimeDayShiftComputationFault TemporalComputationResult :=
  match operation.shift.evaluateThen operation.nextAmount .computation input with
  | .error error => .error (.shift error)
  | .ok result => .ok result.asTemporalComputationResult

/-- Execute the bounded field-backed result through declaration-owned rendering. -/
def evaluateOutcome (operation : CheckedDateTimeTwoDayShiftComputation model)
    (input : CheckedDocument model) :
    Except DateTimeDayShiftComputationFault DateTimeTargetOutcome :=
  match operation.evaluateOperand input with
  | .error error => .error error
  | .ok result => operation.target.evaluate result |>.mapError .target

/-- Execute and classify the rich target outcome against the immutable source. -/
def executeResult (operation : CheckedDateTimeTwoDayShiftComputation model)
    (input : CheckedDocument model)
    (residualMessages : List ResidualMessage) :
    Except DateTimeDayShiftComputationFault
      (DateTimeComputationRunView ResidualMessage) := do
  let outcome ← operation.evaluateOutcome input
  pure (DateTimeComputationRunView.fromOutcomes input residualMessages
    [(operation.target.checked.target.id, outcome)])

end CheckedDateTimeTwoDayShiftComputation

namespace CheckedNowDateTimeTwoDayShiftComputation

/-- Sample this call's world, run both day amounts, and retain the exact result. -/
def evaluateOperand (operation : CheckedNowDateTimeTwoDayShiftComputation model)
    (world : World) (input : CheckedDocument model) :
    Except DateTimeDayShiftComputationFault TemporalComputationResult :=
  match operation.shift.evaluateThen operation.nextAmount
      .computation world input with
  | .error error => .error (.shift error)
  | .ok result => .ok result.asTemporalComputationResult

/-- Execute the bounded dynamic result through declaration-owned DateTime rendering. -/
def evaluateOutcome
    (operation : CheckedNowDateTimeTwoDayShiftComputation model)
    (world : World) (input : CheckedDocument model) :
    Except DateTimeDayShiftComputationFault DateTimeTargetOutcome :=
  match operation.evaluateOperand world input with
  | .error error => .error error
  | .ok result => operation.target.evaluate result |>.mapError .target

/-- Execute and classify the rich target outcome against the immutable source. -/
def executeResult
    (operation : CheckedNowDateTimeTwoDayShiftComputation model)
    (world : World) (input : CheckedDocument model)
    (residualMessages : List ResidualMessage) :
    Except DateTimeDayShiftComputationFault
      (DateTimeComputationRunView ResidualMessage) := do
  let outcome ← operation.evaluateOutcome world input
  pure (DateTimeComputationRunView.fromOutcomes input residualMessages
    [(operation.target.checked.target.id, outcome)])

end CheckedNowDateTimeTwoDayShiftComputation

end A12Kernel
