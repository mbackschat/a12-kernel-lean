import A12Kernel.Elaboration.TemporalValueComputationApplication
import A12Kernel.Elaboration.TemporalTargetPolicy
import A12Kernel.Elaboration.ValueAsDateTimeWorldComponents
import A12Kernel.Semantics.TimeConstruction

/-! # Checked `Time(...)` target execution

This capsule certifies and executes one bounded nonrepeatable `Time(...)` prefix, either document-only or explicitly world-dependent, through an exact `HH:mm:ss` target, source-relative result classification, and exact scalar application. The clock remains zone-free; the runtime's 1970 date is only a transport representation. Wider formats, repeatable targets, scheduling, and message construction remain separate.
-/

namespace A12Kernel

/-- Static refusal before one checked component-backed Time computation can execute. -/
inductive TimeConstructionComputationElabError where
  | components (error : TimeComponentsElabError)
  | target (error : TimeTargetElabError)
  | targetSelfReference (field : FieldId)
  deriving Repr, DecidableEq

/-- One checked nonrepeatable Time component prefix and its distinct exact target. -/
structure CheckedTimeConstructionComputation (model : FlatModel) where
  components : CheckedTimeComponents model
  target : CheckedTimeTarget model
  targetNotReferenced :
    components.referencesField target.checked.target.id = false

/-- Pair an already-checked component prefix with its exact Time target and reject every direct or nested dependency on that target. -/
def certifyTimeConstructionComputation
    (model : FlatModel) (components : CheckedTimeComponents model)
    (targetField : FieldId) :
    Except TimeConstructionComputationElabError
      (CheckedTimeConstructionComputation model) := do
  let target ←
    elaborateTimeTarget model targetField |>.mapError .target
  if hReference :
      components.referencesField target.checked.target.id = true then
    throw (.targetSelfReference targetField)
  else
    pure {
      components
      target
      targetNotReferenced := by simpa using hReference
    }

/-- Check one surface component prefix, then certify it against its exact Time target. -/
def elaborateTimeConstructionComputation
    (model : FlatModel) (components : SurfaceTimeComponents)
    (targetField : FieldId) :
    Except TimeConstructionComputationElabError
      (CheckedTimeConstructionComputation model) := do
  let checkedComponents ←
    elaborateTimeComponents model components |>.mapError .components
  certifyTimeConstructionComputation model checkedComponents targetField

/-- Static refusal before one checked world-dependent Time computation can execute. -/
inductive WorldTimeConstructionComputationElabError where
  | target (error : TimeTargetElabError)
  | targetSelfReference (field : FieldId)
  deriving Repr, DecidableEq

/-- One checked world-aware Time component prefix and its distinct exact target. -/
structure CheckedWorldTimeConstructionComputation (model : FlatModel) where
  components : CheckedWorldTimeComponents model
  target : CheckedTimeTarget model
  targetNotReferenced :
    components.referencesField target.checked.target.id = false

/-- Pair an already-checked world-aware component prefix with its exact Time target and reject every static or dynamic dependency on that target. -/
def certifyWorldTimeConstructionComputation
    (model : FlatModel) (components : CheckedWorldTimeComponents model)
    (targetField : FieldId) :
    Except WorldTimeConstructionComputationElabError
      (CheckedWorldTimeConstructionComputation model) := do
  let target ←
    elaborateTimeTarget model targetField |>.mapError .target
  if hReference :
      components.referencesField target.checked.target.id = true then
    throw (.targetSelfReference targetField)
  else
    pure {
      components
      target
      targetNotReferenced := by simpa using hReference
    }

namespace TimeConstructionResult

/-- Forget construction-only no-value reasons while retaining value and poison. -/
def asTimeComputationResult : TimeConstructionResult → TimeComputationResult
  | .value time => .value time
  | .unavailable cause => .poison cause
  | .incomplete | .unreal | .nonRelevant => .noValue

end TimeConstructionResult

namespace CheckedTimeTarget

/-- Render one selected Time result; every admitted clock passes the exact target basic check. -/
def evaluate (target : CheckedTimeTarget model) :
    TimeComputationResult → TimeTargetOutcome
  | .noValue => .noValue
  | .poison cause => .poison cause
  | .value time => .accepted (target.format.render time)

end CheckedTimeTarget

namespace CheckedTimeConstructionComputation

/-- Evaluate the checked component prefix in generated computation-phase order. -/
def evaluateConstruction
    (operation : CheckedTimeConstructionComputation model)
    (input : CheckedDocument model) :
    Except TimeComponentsFault TimeConstructionResult :=
  operation.components.evaluate .computation input

/-- Carry the reason-bearing construction through the exact checked Time target. -/
def evaluateOutcome
    (operation : CheckedTimeConstructionComputation model)
    (input : CheckedDocument model) :
    Except TimeComponentsFault TimeTargetOutcome :=
  operation.evaluateConstruction input |>.map fun result =>
    operation.target.evaluate result.asTimeComputationResult

/-- Execute and classify the one rich target outcome against the immutable source document. -/
def executeResult
    (operation : CheckedTimeConstructionComputation model)
    (input : CheckedDocument model)
    (residualMessages : List ResidualMessage) :
    Except TimeComponentsFault (TimeComputationRunView ResidualMessage) := do
  let outcome ← operation.evaluateOutcome input
  pure (TimeComputationRunView.fromOutcomes input residualMessages
    [(operation.target.checked.target.id, outcome)])

end CheckedTimeConstructionComputation

namespace CheckedWorldTimeConstructionComputation

/-- Evaluate the checked world-aware component prefix in generated computation-phase order against the caller-supplied world. -/
def evaluateConstruction
    (operation : CheckedWorldTimeConstructionComputation model)
    (world : World) (input : CheckedDocument model) :
    Except TimeComponentsFault TimeConstructionResult :=
  operation.components.evaluate .computation world input

/-- Carry the reason-bearing world-aware construction through the exact checked Time target. -/
def evaluateOutcome
    (operation : CheckedWorldTimeConstructionComputation model)
    (world : World) (input : CheckedDocument model) :
    Except TimeComponentsFault TimeTargetOutcome :=
  operation.evaluateConstruction world input |>.map fun result =>
    operation.target.evaluate result.asTimeComputationResult

/-- Execute and classify one world-aware rich target outcome against the immutable source document. -/
def executeResult
    (operation : CheckedWorldTimeConstructionComputation model)
    (world : World) (input : CheckedDocument model)
    (residualMessages : List ResidualMessage) :
    Except TimeComponentsFault (TimeComputationRunView ResidualMessage) := do
  let outcome ← operation.evaluateOutcome world input
  pure (TimeComputationRunView.fromOutcomes input residualMessages
    [(operation.target.checked.target.id, outcome)])

end CheckedWorldTimeConstructionComputation

/-- Exact caller-supplied Time destination. -/
abbrev TimeComputationDestination :=
  TemporalComputationDestination StoredTime

namespace TimeComputationDestination

/-- Specialize the existing one-target transition at one Time field. -/
def applyOutcome (destination : TimeComputationDestination)
    (target : FieldId) (outcome : TimeTargetOutcome) :
    TimeComputationDestination :=
  TemporalComputationDestination.update destination target
    (outcome.applyTo (destination target))

/-- Apply one source-classified CLEARED action without reclassifying it against the destination. -/
def applyRetainedClear (destination : TimeComputationDestination)
    (target : FieldId) : TimeComputationDestination :=
  TemporalComputationDestination.applyRetainedClear destination target

end TimeComputationDestination

namespace TimeComputationRunView

/-- Targets consumed by Time application; unchanged successes and residual messages are absent. -/
def actionTargets (view : TimeComputationRunView ResidualMessage) :
    List FieldId :=
  TemporalValueComputationRunView.actionTargets view

/-- Apply clears before changed values; unchanged successes and residual messages never mutate the destination. -/
def applyTo (view : TimeComputationRunView ResidualMessage)
    (destination : TimeComputationDestination) :
    Except TemporalValueComputationApplicationError
      TimeComputationDestination :=
  TemporalValueComputationRunView.applyTo view destination
    TimeComputationDestination.applyRetainedClear
    (fun current target value =>
      current.applyOutcome target (.accepted value))

end TimeComputationRunView

end A12Kernel
