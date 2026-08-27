import A12Kernel.Elaboration.AddressedRepeatableTarget
import A12Kernel.Elaboration.TemporalValueComputationApplication
import A12Kernel.Elaboration.TemporalTargetPolicy
import A12Kernel.Elaboration.ValueAsDateTimeWorldComponents
import A12Kernel.Semantics.TimeConstruction

/-! # Checked `Time(...)` target execution

This capsule certifies and executes bounded `Time(...)` prefixes through an exact `HH:mm:ss` target. Nonrepeatable prefixes may read checked document or world-dependent components and use scalar result/application. A repeatable prefix currently admits constants only, executes at every physical target row, and retains exact-address result/application. The clock remains zone-free; the runtime's 1970 date is only a transport representation. Wider formats, field-backed repeatable components, scheduling, and message construction remain separate.
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

/-- Constant-only component syntax for one repeatable `Time(...)` target. Field-backed components require a separate addressed operand certificate. -/
abbrev SurfaceAddressedTimeConstantComponents := TimeComponentPrefix String

/-- Position-checked constants for one repeatable `Time(...)` target. -/
abbrev CheckedAddressedTimeConstantComponents := TimeComponentPrefix Int

inductive AddressedTimeConstantConstructionElabError where
  | target (cause : ResolveError)
  | targetOutsideDeclaringGroup (path declaringGroup : GroupPath)
  | targetNotRepeatable (path : List String)
  | targetPolicy (cause : TimeTargetElabError)
  | component (cause : TimeComponentsElabError)
  deriving Repr, DecidableEq

private def mapAddressedTimeConstructionTargetError :
    AddressedRepeatableTargetElabError →
      AddressedTimeConstantConstructionElabError
  | .target cause => .target cause
  | .targetOutsideDeclaringGroup path declaringGroup =>
      .targetOutsideDeclaringGroup path declaringGroup
  | .targetNotRepeatable path => .targetNotRepeatable path

private def decodeAddressedTimeConstant (position : TimeComponentPosition)
    (source : String) : Except TimeComponentsElabError Int :=
  match position.decodeConstant? source with
  | some value => pure value
  | none => throw (.constantNotAdmitted position source)

private def checkAddressedTimeConstantComponents :
    SurfaceAddressedTimeConstantComponents →
      Except TimeComponentsElabError CheckedAddressedTimeConstantComponents
  | .empty => pure .empty
  | .hour hour => .hour <$> decodeAddressedTimeConstant .hour hour
  | .minute hour minute =>
      .minute <$> decodeAddressedTimeConstant .hour hour <*>
        decodeAddressedTimeConstant .minute minute
  | .second hour minute second =>
      .second <$> decodeAddressedTimeConstant .hour hour <*>
        decodeAddressedTimeConstant .minute minute <*>
        decodeAddressedTimeConstant .second second

/-- One repeatable complete-Time target and a zero-through-three constant component prefix. -/
structure CheckedAddressedTimeConstantConstructionComputation
    (model : FlatModel) where
  private mk ::
  checkedTarget : CheckedAddressedRepeatableTarget model
  target : CheckedTimeTarget model
  components : CheckedAddressedTimeConstantComponents

/-- Check target placement and exact Time policy before decoding each constant in authored component order. -/
def checkAddressedTimeConstantConstructionComputation
    (model : FlatModel) (declaringGroup : GroupPath) (targetField : FieldId)
    (authored : SurfaceAddressedTimeConstantComponents) :
    Except AddressedTimeConstantConstructionElabError
      (CheckedAddressedTimeConstantConstructionComputation model) := do
  let checkedTarget ←
    checkAddressedRepeatableTarget model declaringGroup targetField
      |>.mapError mapAddressedTimeConstructionTargetError
  let target ← elaborateTimeTargetIn model
    checkedTarget.declaration.repeatableScope targetField
      |>.mapError .targetPolicy
  let components ←
    checkAddressedTimeConstantComponents authored |>.mapError .component
  pure { checkedTarget, target, components }

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
  pure (TimeComputationRunView.fromScalarConstructionOutcomes input residualMessages
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
  pure (TimeComputationRunView.fromScalarConstructionOutcomes input residualMessages
    [(operation.target.checked.target.id, outcome)])

end CheckedWorldTimeConstructionComputation

namespace CheckedAddressedTimeConstantComponents

/-- Evaluate an already-decoded constant prefix. Every omitted trailing component is the constructor-owned zero. -/
def evaluate : CheckedAddressedTimeConstantComponents → TimeConstructionResult
  | .empty => TimeConstructionArity.zero.evaluate .empty .empty .empty
  | .hour hour =>
      TimeConstructionArity.hour.evaluate (.value hour) .empty .empty
  | .minute hour minute =>
      TimeConstructionArity.minute.evaluate
        (.value hour) (.value minute) .empty
  | .second hour minute second =>
      TimeConstructionArity.second.evaluate
        (.value hour) (.value minute) (.value second)

end CheckedAddressedTimeConstantComponents

inductive AddressedTimeConstantConstructionFault where
  | targetRows (cause : ActualRowEnvironmentError)
  | targetEnvironment (cause : EnvBindingError)
  deriving Repr, DecidableEq

structure AddressedTimeConstantConstructionOutcome where
  targetField : CellAddr
  outcome : TimeTargetOutcome
  deriving Repr, DecidableEq

structure AddressedTimeConstantConstructionRunView (model : FlatModel)
    (ResidualMessage : Type) where
  private mk ::
  operation : CheckedAddressedTimeConstantConstructionComputation model
  time : TimeComputationRunView ResidualMessage CellAddr

namespace CheckedAddressedTimeConstantConstructionComputation

def evaluateOutcome
    (operation : CheckedAddressedTimeConstantConstructionComputation model) :
    TimeTargetOutcome :=
  operation.target.evaluate operation.components.evaluate.asTimeComputationResult

private def evaluateAt
    (operation : CheckedAddressedTimeConstantConstructionComputation model)
    (environment : Env) :
    Except AddressedTimeConstantConstructionFault
      AddressedTimeConstantConstructionOutcome := do
  let path ← environment.pathForScope
    operation.checkedTarget.declaration.repeatableScope
      |>.mapError .targetEnvironment
  pure {
    targetField := { field := operation.checkedTarget.targetField, path }
    outcome := operation.evaluateOutcome }

/-- Execute the constant construction once at every physical target row in document order. -/
def execute
    (operation : CheckedAddressedTimeConstantConstructionComputation model)
    (input : CheckedDocument model) :
    Except AddressedTimeConstantConstructionFault
      (List AddressedTimeConstantConstructionOutcome) := do
  let environments ← input.actualRowEnvironments
    operation.checkedTarget.declaration.repeatableScope
      |>.mapError .targetRows
  environments.mapM operation.evaluateAt

/-- Classify exact row outcomes by ordinary immutable-source clock equality. The scalar constructor's always-changed exception does not cross this repeatable boundary. -/
def executeResult
    (operation : CheckedAddressedTimeConstantConstructionComputation model)
    (input : CheckedDocument model) (residualMessages : List ResidualMessage) :
    Except AddressedTimeConstantConstructionFault
      (AddressedTimeConstantConstructionRunView model ResidualMessage) := do
  let outcomes ← operation.execute input
  pure {
    operation
    time := TimeComputationRunView.fromOutcomesAt
      input.sourceTimeTargetStateAt residualMessages
      (outcomes.map fun entry => (entry.targetField, entry.outcome)) }

end CheckedAddressedTimeConstantConstructionComputation

/-- Exact caller-supplied Time destination over a scalar or addressed target-key domain. -/
abbrev TimeComputationDestination (Target : Type := FieldId) :=
  TemporalComputationDestination StoredTime Target

namespace TimeComputationDestination

/-- Specialize the existing one-target transition at one Time field. -/
def applyOutcome {Target : Type} [DecidableEq Target]
    (destination : TimeComputationDestination Target)
    (target : Target) (outcome : TimeTargetOutcome) :
    TimeComputationDestination Target :=
  TemporalComputationDestination.update destination target
    (outcome.applyTo (destination target))

/-- Apply one source-classified CLEARED action without reclassifying it against the destination. -/
def applyRetainedClear {Target : Type} [DecidableEq Target]
    (destination : TimeComputationDestination Target)
    (target : Target) : TimeComputationDestination Target :=
  TemporalComputationDestination.applyRetainedClear destination target

end TimeComputationDestination

namespace TimeComputationRunView

/-- Targets consumed by Time application; unchanged successes and residual messages are absent. -/
def actionTargets {Target : Type}
    (view : TimeComputationRunView ResidualMessage Target) :
    List Target :=
  TemporalValueComputationRunView.actionTargets view

/-- Apply clears before changed values; unchanged successes and residual messages never mutate the destination. -/
def applyTo {Target : Type} [DecidableEq Target]
    (view : TimeComputationRunView ResidualMessage Target)
    (destination : TimeComputationDestination Target) :
    Except (TemporalValueComputationApplicationError Target)
      (TimeComputationDestination Target) :=
  TemporalValueComputationRunView.applyTo view destination
    TimeComputationDestination.applyRetainedClear
    (fun current target value =>
      current.applyOutcome target (.accepted value))

/-- Fail-closed errors for checked nonrepeatable Time destination projection. -/
inductive TimeComputationCheckedApplicationError where
  | duplicateActionTarget (field : FieldId)
  | targetField (field : FieldId) (cause : ResolveError)
  | nonTimeTarget (field : FieldId)
  | repeatableTarget (field : FieldId)
  deriving Repr, DecidableEq

private def acceptsActionKind : FieldKind → Bool
  | .temporal .time components => components == TemporalComponents.time
  | _ => false

def validateActionTargets (model : FlatModel) (targets : List FieldId) :
    Except TimeComputationCheckedApplicationError Unit :=
  TemporalComputationApplicationTarget.validateAllNonrepeatable
    model acceptsActionKind
    TimeComputationCheckedApplicationError.targetField
    TimeComputationCheckedApplicationError.nonTimeTarget
    TimeComputationCheckedApplicationError.repeatableTarget targets

/-- Apply one retained nonrepeatable Time result to the exact root Time-state projection of a separately supplied checked destination. The retained result is not model-indexed, so source/destination model compatibility remains a caller precondition. -/
def applyToChecked (view : TimeComputationRunView ResidualMessage)
    (destination : CheckedDocument model) :
    Except TimeComputationCheckedApplicationError TimeComputationDestination :=
  match FieldId.firstDuplicate? view.actionTargets with
  | some duplicate => .error (.duplicateActionTarget duplicate)
  | none => do
      validateActionTargets model view.actionTargets
      (view.applyTo destination.sourceTimeTargetState).mapError
        (fun | .duplicateActionTarget duplicate => .duplicateActionTarget duplicate)

end TimeComputationRunView

namespace AddressedTimeConstantConstructionRunView

/-- Apply only retained row-local changes to a separate same-model destination projection. -/
def applyToChecked
    (view : AddressedTimeConstantConstructionRunView model ResidualMessage)
    (destination : CheckedDocument model) :
    Except (TemporalValueComputationApplicationError CellAddr)
      (TimeComputationDestination CellAddr) :=
  view.time.applyTo destination.sourceTimeTargetStateAt

end AddressedTimeConstantConstructionRunView

end A12Kernel
