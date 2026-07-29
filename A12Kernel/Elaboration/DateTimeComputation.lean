import A12Kernel.Elaboration.DateTimeComputationApplication
import A12Kernel.Elaboration.ValueAsDateTimeExtraction

/-! # Checked dynamic DateTime computations

This capsule admits dynamic `Now`, directly or after one checked `AddHours`,
`AddMinutes`, or `AddSeconds`, against one bounded complete DateTime target. Checked
operations retain no clock sample: each evaluation reads the exact instant from its
explicit `World`, then delegates model-zone rendering to `CheckedDateTimeTarget`.

The shifted form reuses the existing checked numeric amount and exact-instant shift. It
is deliberately separate from the field-backed carrier because its source is execution
state rather than a document field. Calendar-day arithmetic, recursion, alternatives,
scheduling, generated validation, and message construction remain separate.
-/

namespace A12Kernel

/-- Static refusal before the bounded `Now` computation can execute. -/
inductive DateTimeComputationElabError where
  | target (error : DateTimeTargetElabError)
  deriving Repr, DecidableEq

/-- Admit only the existing dynamic `Now` operand in this first DateTime computation boundary. -/
def FlatModel.admitsDateTimeComputationOperand
    (_model : FlatModel) : FlatTemporalOperand → Bool
  | .nowValue => true
  | _ => false

/-- One model-certified `Now` computation and its declaration-owned DateTime target. -/
structure CheckedDateTimeComputation (model : FlatModel) where
  operand : FlatTemporalOperand
  target : CheckedDateTimeTarget model
  operandAdmitted :
    model.admitsDateTimeComputationOperand operand = true

/-- Resolve one dynamic `Now` operand and one model-owned nonrepeatable DateTime target. No clock value is sampled during elaboration. -/
def elaborateDateTimeNowComputation
    (model : FlatModel) (targetField : FieldId) :
    Except DateTimeComputationElabError
      (CheckedDateTimeComputation model) := do
  let target ←
    elaborateDateTimeTarget model targetField |>.mapError .target
  pure {
    operand := .nowValue
    target
    operandAdmitted := rfl }

/-- Structural target-rendering failure outside the rich DateTime result domain. -/
inductive DateTimeComputationFault where
  | target (error : DateTimeTargetEvaluationFault)
  deriving Repr, DecidableEq

namespace CheckedDateTimeComputation

/-- Read the exact `Now` instant from this execution's explicit world. -/
def evaluateOperand (_operation : CheckedDateTimeComputation model)
    (world : World) : TemporalComputationResult :=
  .value world.now

/-- Execute the dynamic operand through the declaration-owned DateTime target. -/
def evaluateOutcome (operation : CheckedDateTimeComputation model)
    (world : World) :
    Except DateTimeComputationFault DateTimeTargetOutcome :=
  operation.target.evaluate (operation.evaluateOperand world)
    |>.mapError .target

end CheckedDateTimeComputation

/-- Static refusal before one dynamic shifted-`Now` DateTime computation can execute. -/
inductive ShiftedNowDateTimeComputationElabError where
  | shift (error : ValueAsDateTimeExtractionElabError)
  | target (error : DateTimeTargetElabError)
  deriving Repr, DecidableEq

/-- One checked shifted-`Now` source and its declaration-owned DateTime target. -/
structure CheckedShiftedNowDateTimeComputation (model : FlatModel) where
  shift : CheckedShiftedNowDateTimeSource model
  target : CheckedDateTimeTarget model

/-- Check one dynamic exact-instant shift and one complete-DateTime target without
    sampling the execution world. -/
def elaborateShiftedNowDateTimeComputation
    (model : FlatModel) (unit : DateTimeSubdayUnit)
    (amount : CheckedTemporalShiftAmount model) (targetField : FieldId) :
    Except ShiftedNowDateTimeComputationElabError
      (CheckedShiftedNowDateTimeComputation model) := do
  let shift ← elaborateShiftedNowDateTimeSource model unit amount
    |>.mapError .shift
  let target ← elaborateDateTimeTarget model targetField |>.mapError .target
  pure { shift, target }

/-- Structural execution failure outside the rich DateTime target outcome. -/
inductive ShiftedNowDateTimeComputationFault where
  | shift (error : ValueAsDateTimeExtractionFault)
  | target (error : DateTimeTargetEvaluationFault)
  deriving Repr, DecidableEq

namespace CheckedShiftedNowDateTimeComputation

/-- Sample this call's exact world once, then execute the checked sub-day shift. -/
def evaluateOperand (operation : CheckedShiftedNowDateTimeComputation model)
    (world : World) (input : CheckedDocument model) :
    Except ShiftedNowDateTimeComputationFault TemporalComputationResult :=
  match operation.shift.evaluate .computation world input with
  | .error error => .error (.shift error)
  | .ok result => .ok result.asTemporalComputationResult

/-- Execute the shifted dynamic operand through declaration-owned DateTime rendering. -/
def evaluateOutcome (operation : CheckedShiftedNowDateTimeComputation model)
    (world : World) (input : CheckedDocument model) :
    Except ShiftedNowDateTimeComputationFault DateTimeTargetOutcome :=
  match operation.evaluateOperand world input with
  | .error error => .error error
  | .ok result => operation.target.evaluate result |>.mapError .target

/-- Execute and classify the rich target outcome against the immutable source. -/
def executeResult (operation : CheckedShiftedNowDateTimeComputation model)
    (world : World) (input : CheckedDocument model)
    (residualMessages : List ResidualMessage) :
    Except ShiftedNowDateTimeComputationFault
      (DateTimeComputationRunView ResidualMessage) := do
  let outcome ← operation.evaluateOutcome world input
  pure (DateTimeComputationRunView.fromOutcomes input residualMessages
    [(operation.target.checked.target.id, outcome)])

end CheckedShiftedNowDateTimeComputation

end A12Kernel
