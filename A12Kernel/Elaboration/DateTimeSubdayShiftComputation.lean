import A12Kernel.Elaboration.DateTimeComputationApplication
import A12Kernel.Elaboration.ValueAsDateTimeExtraction

/-! # Checked DateTime sub-day computations

This capsule executes one direct field-backed `AddHours`, `AddMinutes`, or `AddSeconds`
through one distinct declaration-owned DateTime target and the existing result/application
path. The shared shift certificate evaluates exact instant-in/instant-out arithmetic
before target rendering; its wall-clock extraction remains a separate projection.

Dynamic shifted `Now`, calendar-day arithmetic, recursion, alternatives, scheduling,
repeatable placement, generated validation, and message construction remain separate.
-/

namespace A12Kernel

/-- Static refusal before one checked DateTime sub-day shift can target a declaration. -/
inductive DateTimeSubdayShiftComputationElabError where
  | shift (error : ValueAsDateTimeExtractionElabError)
  | target (error : DateTimeTargetElabError)
  | targetSelfReference (field : FieldId)
  deriving Repr, DecidableEq

/-- One checked field-backed sub-day shift and its distinct DateTime target. -/
structure CheckedDateTimeSubdayShiftComputation (model : FlatModel) where
  shift : CheckedShiftedDateTimeSource model
  target : CheckedDateTimeTarget model
  sourceDistinct : shift.source.id ≠ target.checked.target.id

/-- Check one field-backed sub-day shift and one distinct complete-DateTime target. -/
def elaborateDateTimeSubdayShiftComputation
    (model : FlatModel) (sourceField : FieldId) (unit : DateTimeSubdayUnit)
    (amount : CheckedTemporalShiftAmount model) (targetField : FieldId) :
    Except DateTimeSubdayShiftComputationElabError
      (CheckedDateTimeSubdayShiftComputation model) := do
  let shift ← elaborateShiftedDateTimeSource model sourceField unit amount
    |>.mapError .shift
  let target ← elaborateDateTimeTarget model targetField |>.mapError .target
  if distinct : shift.source.id = target.checked.target.id then
    throw (.targetSelfReference targetField)
  else
    pure { shift, target, sourceDistinct := distinct }

/-- Structural execution failure outside the rich DateTime target outcome. -/
inductive DateTimeSubdayShiftComputationFault where
  | shift (error : ValueAsDateTimeExtractionFault)
  | target (error : DateTimeTargetEvaluationFault)
  deriving Repr, DecidableEq

namespace CheckedDateTimeSubdayShiftComputation

/-- Execute the checked exact-instant shift in computation phase. -/
def evaluateOperand (operation : CheckedDateTimeSubdayShiftComputation model)
    (input : CheckedDocument model) :
    Except DateTimeSubdayShiftComputationFault TemporalComputationResult :=
  match operation.shift.evaluate .computation input with
  | .error error => .error (.shift error)
  | .ok result => .ok result.asTemporalComputationResult

/-- Execute the checked shift through declaration-owned DateTime rendering. -/
def evaluateOutcome (operation : CheckedDateTimeSubdayShiftComputation model)
    (input : CheckedDocument model) :
    Except DateTimeSubdayShiftComputationFault DateTimeTargetOutcome :=
  match operation.evaluateOperand input with
  | .error error => .error error
  | .ok result => operation.target.evaluate result |>.mapError .target

/-- Execute and classify the one rich target outcome against the immutable source. -/
def executeResult (operation : CheckedDateTimeSubdayShiftComputation model)
    (input : CheckedDocument model) (residualMessages : List ResidualMessage) :
    Except DateTimeSubdayShiftComputationFault
      (DateTimeComputationRunView ResidualMessage) := do
  let outcome ← operation.evaluateOutcome input
  pure (DateTimeComputationRunView.fromOutcomes input residualMessages
    [(operation.target.checked.target.id, outcome)])

end CheckedDateTimeSubdayShiftComputation

end A12Kernel
