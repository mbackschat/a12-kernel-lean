import A12Kernel.Elaboration.TemporalTargetPolicy

/-! # Checked `Now` DateTime computation

This capsule admits the existing dynamic `Now` operand against one bounded complete DateTime target. The checked operation retains no clock sample: each evaluation reads the exact instant from its explicit `World`, then delegates model-zone rendering to `CheckedDateTimeTarget`. Field operands, arithmetic, alternatives, scheduling, result classification, application, and generated validation remain separate.
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

end A12Kernel
