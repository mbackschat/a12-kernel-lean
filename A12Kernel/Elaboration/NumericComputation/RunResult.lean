import A12Kernel.Elaboration.NumericComputation.Run
import A12Kernel.Elaboration.NumericComputation.SourceTarget
import A12Kernel.Semantics.NumericComputationRunResult

/-! # Checked-document and execution adapters for Number result classification -/

namespace A12Kernel

namespace NumericComputationRunView

/-- Attach immutable source state to each rich run outcome, then build its pre-assembly projection. -/
def fromOutcomes (input : CheckedDocument model)
    (payloadAt : FieldId → Payload)
    (supplied : List (ComputationFormalMessage Payload))
    (outcomes : List (FieldId × NumericTargetOutcome)) :
    Except NumericSourceTargetError
      (NumericComputationRunView (ComputationFormalMessage Payload)) := do
  let entries ← outcomes.mapM fun (targetField, outcome) => do
    let source ← input.numericTargetState targetField
    pure { targetField, outcome, source }
  pure (fromSourceOutcomesWithMessages
    (fun field => MessagePointer.ofCellAddr { field, path := [] })
    payloadAt supplied entries)

end NumericComputationRunView

inductive NumericComputationRunResultFault where
  | execution (cause : NumericComputationRunFault)
  | sourceTarget (cause : NumericSourceTargetError)
  deriving Repr, DecidableEq

namespace CheckedNumericComputationRun

/-- Execute the checked run and classify its outcomes relative to the immutable source. This low-level projection precedes diagnostic assembly. -/
def executeResult (run : CheckedNumericComputationRun model)
    (world : World) (input : CheckedDocument model)
    (payloadAt : FieldId → Payload)
    (supplied : List (ComputationFormalMessage Payload)) :
    Except NumericComputationRunResultFault
      (NumericComputationRunView (ComputationFormalMessage Payload)) := do
  let outcomes ← (run.execute world input).mapError .execution
  (NumericComputationRunView.fromOutcomes input payloadAt supplied outcomes).mapError
    .sourceTarget

end CheckedNumericComputationRun

end A12Kernel
