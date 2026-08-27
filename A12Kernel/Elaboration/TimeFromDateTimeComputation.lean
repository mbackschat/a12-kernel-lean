import A12Kernel.Elaboration.TimeComputation
import A12Kernel.Elaboration.ValueAsDateTimeExtraction

/-! # Checked scalar `TimeFromDateTime` target execution

This capsule carries one already-classified complete DateTime source through the existing wall-clock projection, exact `HH:mm:ss` Time target, five-channel Time result, and checked scalar application. Repeatable placement, scheduling, materialized documents, and later validation remain separate.
-/

namespace A12Kernel

/-- Static refusal before one scalar `TimeFromDateTime` computation can execute. -/
inductive TimeFromDateTimeComputationElabError where
  | source (error : ValueAsDateTimeExtractionElabError)
  | target (error : TimeTargetElabError)
  deriving Repr, DecidableEq

/-- One checked complete-DateTime source paired with the existing declaration-owned Time target. -/
structure CheckedTimeFromDateTimeComputation (model : FlatModel) where
  source : CheckedDateTimeSource model
  target : CheckedTimeTarget model

/-- Resolve one nonrepeatable complete-DateTime source and one complete Time target in the same model. -/
def elaborateTimeFromDateTimeComputation
    (model : FlatModel) (sourceField targetField : FieldId) :
    Except TimeFromDateTimeComputationElabError
      (CheckedTimeFromDateTimeComputation model) := do
  let source ← elaborateDateTimeSource model sourceField |>.mapError .source
  let target ← elaborateTimeTarget model targetField |>.mapError .target
  pure { source, target }

namespace ValueAsDateTimeTimeOperand

/-- Forget construction-only omission provenance while retaining the extracted clock and exact formal cause. -/
def asTimeComputationResult :
    ValueAsDateTimeTimeOperand → TimeComputationResult
  | .value time _ => .value time
  | .unavailable cause => .poison cause
  | .noValue _ | .nonRelevant => .noValue

end ValueAsDateTimeTimeOperand

namespace CheckedDateTimeSource

/-- Read one checked scalar complete-DateTime source and retain its wall clock, clean absence, or exact formal cause. -/
def readTime (source : CheckedDateTimeSource model)
    (phase : Phase) (input : CheckedDocument model) :
    Except ValueAsDateTimeExtractionFault ValueAsDateTimeTimeOperand :=
  readTimeFromDateTimeSource source.source phase input

end CheckedDateTimeSource

namespace CheckedTimeFromDateTimeComputation

/-- Evaluate the source once at computation phase and project its retained wall clock into the Time result domain. -/
def evaluateOperand (operation : CheckedTimeFromDateTimeComputation model)
    (input : CheckedDocument model) :
    Except ValueAsDateTimeExtractionFault TimeComputationResult :=
  operation.source.readTime .computation input
    |>.map ValueAsDateTimeTimeOperand.asTimeComputationResult

/-- Carry the projected wall clock through the existing declaration-owned Time target. -/
def evaluateOutcome (operation : CheckedTimeFromDateTimeComputation model)
    (input : CheckedDocument model) :
    Except ValueAsDateTimeExtractionFault TimeTargetOutcome :=
  operation.evaluateOperand input |>.map operation.target.evaluate

/-- Project the checked outcome through the ordinary scalar Time result collections. -/
def executeResult (operation : CheckedTimeFromDateTimeComputation model)
    (input : CheckedDocument model) (residualMessages : List ResidualMessage) :
    Except ValueAsDateTimeExtractionFault
      (TimeComputationRunView ResidualMessage) := do
  let outcome ← operation.evaluateOutcome input
  pure (TimeComputationRunView.fromOutcomes input residualMessages
    [(operation.target.checked.target.id, outcome)])

end CheckedTimeFromDateTimeComputation

end A12Kernel
