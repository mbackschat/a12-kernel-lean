import A12Kernel.Elaboration.AddressedRepeatableTarget
import A12Kernel.Elaboration.TemporalValueComputationApplication
import A12Kernel.Elaboration.TemporalTargetPolicy
import A12Kernel.Elaboration.ValueAsDateTimeWorldComponents
import A12Kernel.Semantics.TimeConstruction

/-! # Checked `Time(...)` target execution

This capsule certifies and executes bounded `Time(...)` prefixes through an exact `HH:mm:ss` target. Nonrepeatable prefixes may read checked document or world-dependent components and use scalar result/application. A repeatable prefix admits constants, Number fields, checked digit-String fields, and matching direct Time or DateTime extractors at any scope bound by the target row, executes at every physical target row, and retains exact-address result/application. The clock remains zone-free; the runtime's 1970 date is only a transport representation. Wider formats, nested extractor expressions, world-backed repeatable components, scheduling, and message construction remain separate.
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

/-- Compatibility surface for the retained constant-only repeatable `Time(...)` route. -/
abbrev SurfaceAddressedTimeConstantComponents := TimeComponentPrefix String

/-- One repeatable `Time(...)` component whose field form is resolved relative to the computation group. -/
inductive SurfaceAddressedTimeComponent where
  | constant (source : String)
  | number (source : SurfaceFieldPath)
  | string (source : SurfaceFieldPath)
  | extractor (part : TimeNumericPart) (source : SurfaceFieldPath)
  deriving Repr, DecidableEq

/-- A zero-through-three repeatable component prefix over quoted constants and checked Number, digit-String, or direct temporal-extractor fields. -/
abbrev SurfaceAddressedTimeComponents :=
  TimeComponentPrefix SurfaceAddressedTimeComponent

/-- One Number component whose declaration policy and repetition scope are certified for the target row. -/
structure CheckedAddressedTimeNumberField (model : FlatModel)
    (targetScope : List RepeatableLevel) where
  position : TimeComponentPosition
  declaringGroup : GroupPath
  reference : SurfaceFieldPath
  declaration : FlatFieldDecl
  source : FlatNumberField
  resolved : model.resolveFieldDeclarationUnchecked declaringGroup reference =
    .ok declaration
  sourceNumber : declaration.toNumberField? = some source
  scopeBound : declaration.repetitionBoundBy targetScope = true
  admitted : model.admitsTimeNumberComponentField position source = true

/-- One digit-String component whose declaration policy and repetition scope are certified for the target row. -/
structure CheckedAddressedTimeStringField (model : FlatModel)
    (targetScope : List RepeatableLevel) where
  position : TimeComponentPosition
  declaringGroup : GroupPath
  reference : SurfaceFieldPath
  declaration : FlatFieldDecl
  source : FlatStringField
  resolved : model.resolveFieldDeclarationUnchecked declaringGroup reference =
    .ok declaration
  sourceString : declaration.toStringValueField? = some source
  scopeBound : declaration.repetitionBoundBy targetScope = true
  admitted : model.admitsTimeStringComponentField source = true

/-- One temporal extractor whose token, declaration, and repetition scope are certified for the target row. -/
structure CheckedAddressedTimeExtractorField (model : FlatModel) (targetScope : List RepeatableLevel) where
  position : TimeComponentPosition
  part : TimeNumericPart
  declaringGroup : GroupPath
  reference : SurfaceFieldPath
  declaration : FlatFieldDecl
  source : FlatTemporalField
  resolved : model.resolveFieldDeclarationUnchecked declaringGroup reference =
    .ok declaration
  sourceTemporal : declaration.toTemporalField? = some source
  scopeBound : declaration.repetitionBoundBy targetScope = true
  admitted : model.admitsTimeExtractorComponentField position part source = true

/-- One checked repeatable component retaining its decoded constant or exact addressed field source. -/
inductive CheckedAddressedTimeComponent (model : FlatModel)
    (targetScope : List RepeatableLevel) where
  | constant (value : Int)
  | number (checked : CheckedAddressedTimeNumberField model targetScope)
  | string (checked : CheckedAddressedTimeStringField model targetScope)
  | extractor (checked : CheckedAddressedTimeExtractorField model targetScope)

namespace CheckedAddressedTimeComponent

def referencesField (component : CheckedAddressedTimeComponent model targetScope)
    (field : FieldId) : Bool :=
  match component with
  | .constant _ => false
  | .number checked => checked.source.id == field
  | .string checked => checked.source.id == field
  | .extractor checked => checked.source.id == field

def fieldDependencies :
    CheckedAddressedTimeComponent model targetScope → List FieldId
  | .constant _ => []
  | .number checked => [checked.source.id]
  | .string checked => [checked.source.id]
  | .extractor checked => [checked.source.id]

end CheckedAddressedTimeComponent

abbrev CheckedAddressedTimeComponents (model : FlatModel)
    (targetScope : List RepeatableLevel) :=
  TimeComponentPrefix (CheckedAddressedTimeComponent model targetScope)

namespace CheckedAddressedTimeComponents

def referencesField (components : CheckedAddressedTimeComponents model targetScope)
    (field : FieldId) : Bool :=
  components.referencesFieldWith CheckedAddressedTimeComponent.referencesField field

def fieldDependencies : CheckedAddressedTimeComponents model targetScope →
    List FieldId
  | .empty => []
  | .hour hour => hour.fieldDependencies
  | .minute hour minute =>
      hour.fieldDependencies ++ minute.fieldDependencies
  | .second hour minute second =>
      hour.fieldDependencies ++ minute.fieldDependencies ++ second.fieldDependencies

end CheckedAddressedTimeComponents

inductive AddressedTimeConstructionComponentElabError where
  | source (position : TimeComponentPosition) (cause : ResolveError)
  | sourceKind (position : TimeComponentPosition) (path : List String)
      (actual : SurfaceScalarKind)
  | sourceScope (target source : List String)
  | targetSelfReference (field : FieldId)
  | declarationNotAdmitted (position : TimeComponentPosition)
      (path : List String)
  | constantNotAdmitted (position : TimeComponentPosition) (source : String)
  | extractorMismatch (position : TimeComponentPosition)
      (actual : TimeNumericPart)
  deriving Repr, DecidableEq

inductive AddressedTimeConstructionElabError where
  | target (cause : ResolveError)
  | targetOutsideDeclaringGroup (path declaringGroup : GroupPath)
  | targetNotRepeatable (path : List String)
  | targetPolicy (cause : TimeTargetElabError)
  | component (cause : AddressedTimeConstructionComponentElabError)
  deriving Repr, DecidableEq

private def mapAddressedTimeConstructionTargetError :
    AddressedRepeatableTargetElabError →
      AddressedTimeConstructionElabError
  | .target cause => .target cause
  | .targetOutsideDeclaringGroup path declaringGroup =>
      .targetOutsideDeclaringGroup path declaringGroup
  | .targetNotRepeatable path => .targetNotRepeatable path

private def decodeAddressedTimeConstant (position : TimeComponentPosition)
    (source : String) : Except AddressedTimeConstructionComponentElabError Int :=
  match position.decodeConstant? source with
  | some value => pure value
  | none => throw (.constantNotAdmitted position source)

/-- Check one addressed component independently so a second carrier can compose it without duplicating declaration or placement rules. -/
def checkAddressedTimeComponent
    (model : FlatModel) (declaringGroup : GroupPath)
    (targetField : FieldId) (targetScope : List RepeatableLevel)
    (targetPath : List String) (position : TimeComponentPosition) :
    SurfaceAddressedTimeComponent →
      Except AddressedTimeConstructionComponentElabError
        (CheckedAddressedTimeComponent model targetScope)
  | .constant source =>
      .constant <$> decodeAddressedTimeConstant position source
  | .number reference =>
      match hResolved :
          model.resolveFieldDeclarationUnchecked declaringGroup reference with
      | .error cause => throw (.source position cause)
      | .ok declaration =>
        if declaration.id == targetField then
          throw (.targetSelfReference targetField)
        else if hScope : declaration.repetitionBoundBy targetScope = true then
          match hNumber : declaration.toNumberField? with
          | none => throw (.sourceKind position declaration.path
              declaration.policy.kind.surfaceKind)
          | some source =>
            if hAdmitted :
                model.admitsTimeNumberComponentField position source = true then
              pure (.number {
                position
                declaringGroup
                reference
                declaration
                source
                resolved := hResolved
                sourceNumber := hNumber
                scopeBound := hScope
                admitted := hAdmitted
              })
            else
              throw (.declarationNotAdmitted position declaration.path)
        else
          throw (.sourceScope targetPath declaration.path)
  | .string reference =>
      match hResolved :
          model.resolveFieldDeclarationUnchecked declaringGroup reference with
      | .error cause => throw (.source position cause)
      | .ok declaration =>
        if declaration.id == targetField then
          throw (.targetSelfReference targetField)
        else if hScope : declaration.repetitionBoundBy targetScope = true then
          match hString : declaration.toStringValueField? with
          | none => throw (.sourceKind position declaration.path
              declaration.policy.kind.surfaceKind)
          | some source =>
            if hAdmitted :
                model.admitsTimeStringComponentField source = true then
              pure (.string {
                position
                declaringGroup
                reference
                declaration
                source
                resolved := hResolved
                sourceString := hString
                scopeBound := hScope
                admitted := hAdmitted
              })
            else
              throw (.declarationNotAdmitted position declaration.path)
        else
          throw (.sourceScope targetPath declaration.path)
  | .extractor part reference =>
      if position.extractor != part then
        throw (.extractorMismatch position part)
      else match hResolved :
          model.resolveFieldDeclarationUnchecked declaringGroup reference with
      | .error cause => throw (.source position cause)
      | .ok declaration =>
        if declaration.id == targetField then
          throw (.targetSelfReference targetField)
        else if hScope : declaration.repetitionBoundBy targetScope = true then
          match hTemporal : declaration.toTemporalField? with
          | none => throw (.sourceKind position declaration.path
              declaration.policy.kind.surfaceKind)
          | some source =>
            if hAdmitted : model.admitsTimeExtractorComponentField
                position part source = true then
              pure (.extractor {
                position
                part
                declaringGroup
                reference
                declaration
                source
                resolved := hResolved
                sourceTemporal := hTemporal
                scopeBound := hScope
                admitted := hAdmitted
              })
            else
              throw (.declarationNotAdmitted position declaration.path)
        else
          throw (.sourceScope targetPath declaration.path)

private def checkAddressedTimeComponents
    (model : FlatModel) (declaringGroup : GroupPath)
    (targetField : FieldId) (targetScope : List RepeatableLevel)
    (targetPath : List String) : SurfaceAddressedTimeComponents →
      Except AddressedTimeConstructionComponentElabError
        (CheckedAddressedTimeComponents model targetScope)
  | .empty => pure .empty
  | .hour hour =>
      .hour <$> checkAddressedTimeComponent model declaringGroup targetField
        targetScope targetPath .hour hour
  | .minute hour minute =>
      .minute <$> checkAddressedTimeComponent model declaringGroup targetField
        targetScope targetPath .hour hour <*>
        checkAddressedTimeComponent model declaringGroup targetField
          targetScope targetPath .minute minute
  | .second hour minute second =>
      .second <$> checkAddressedTimeComponent model declaringGroup targetField
        targetScope targetPath .hour hour <*>
        checkAddressedTimeComponent model declaringGroup targetField
          targetScope targetPath .minute minute <*>
        checkAddressedTimeComponent model declaringGroup targetField
          targetScope targetPath .second second

/-- One repeatable complete-Time target and a zero-through-three addressed component prefix. -/
structure CheckedAddressedTimeConstructionComputation
    (model : FlatModel) where
  private mk ::
  checkedTarget : CheckedAddressedRepeatableTarget model
  target : CheckedTimeTarget model
  components : CheckedAddressedTimeComponents model
    checkedTarget.declaration.repeatableScope
  targetNotReferenced :
    components.referencesField checkedTarget.targetField = false

/-- Check target placement and exact Time policy before resolving each constant, Number, String, or direct temporal-extractor component in authored order. -/
def checkAddressedTimeConstructionComputation
    (model : FlatModel) (declaringGroup : GroupPath) (targetField : FieldId)
    (authored : SurfaceAddressedTimeComponents) :
    Except AddressedTimeConstructionElabError
      (CheckedAddressedTimeConstructionComputation model) := do
  let checkedTarget ←
    checkAddressedRepeatableTarget model declaringGroup targetField
      |>.mapError mapAddressedTimeConstructionTargetError
  let target ← elaborateTimeTargetIn model
    checkedTarget.declaration.repeatableScope targetField
      |>.mapError .targetPolicy
  let components ← checkAddressedTimeComponents model declaringGroup targetField
    checkedTarget.declaration.repeatableScope checkedTarget.declaration.path authored
      |>.mapError .component
  if hReference : components.referencesField checkedTarget.targetField = true then
    throw (.component (.targetSelfReference checkedTarget.targetField))
  else
    pure {
      checkedTarget
      target
      components
      targetNotReferenced := by simpa using hReference
    }

private def liftAddressedTimeConstants :
    SurfaceAddressedTimeConstantComponents → SurfaceAddressedTimeComponents
  | .empty => .empty
  | .hour hour => .hour (.constant hour)
  | .minute hour minute =>
      .minute (.constant hour) (.constant minute)
  | .second hour minute second =>
      .second (.constant hour) (.constant minute) (.constant second)

/-- Check target placement and exact Time policy before decoding each constant in authored component order. -/
def checkAddressedTimeConstantConstructionComputation
    (model : FlatModel) (declaringGroup : GroupPath) (targetField : FieldId)
    (authored : SurfaceAddressedTimeConstantComponents) :
    Except AddressedTimeConstructionElabError
      (CheckedAddressedTimeConstructionComputation model) :=
  checkAddressedTimeConstructionComputation model declaringGroup targetField
    (liftAddressedTimeConstants authored)

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

/-- Exact authored-order dependencies of the world-aware scalar prefix. -/
def fieldDependencies
    (operation : CheckedWorldTimeConstructionComputation model) : List FieldId :=
  operation.components.fieldDependencies

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

inductive AddressedTimeConstructionFault where
  | targetRows (cause : ActualRowEnvironmentError)
  | targetEnvironment (cause : EnvBindingError)
  | sourceEnvironment (field : FieldId) (cause : EnvBindingError)
  | amountAddressing (cause : CheckedAddressingError)
  | component (cause : TimeComponentsFault)
  deriving Repr, DecidableEq

structure AddressedTimeConstructionOutcome where
  targetField : CellAddr
  outcome : TimeTargetOutcome
  deriving Repr, DecidableEq

structure AddressedTimeConstructionRunView (model : FlatModel)
    (ResidualMessage : Type) where
  private mk ::
  operation : CheckedAddressedTimeConstructionComputation model
  time : TimeComputationRunView ResidualMessage CellAddr

namespace CheckedAddressedTimeNumberField

def read (checked : CheckedAddressedTimeNumberField model targetScope)
    (input : CheckedDocument model) (environment : Env) :
    Except AddressedTimeConstructionFault TimeConstructionComponent := do
  let path ← environment.pathForScope checked.declaration.repeatableScope
    |>.mapError (.sourceEnvironment checked.source.id)
  let cell ← input.read { field := checked.source.id, path }
    |>.mapError (fun cause => .component (.document cause))
  CheckedTimeNumberField.classifyTimeNumberComponent checked.source.id
    (observeCell .computation cell) |>.mapError .component

end CheckedAddressedTimeNumberField

namespace CheckedAddressedTimeStringField

def read (checked : CheckedAddressedTimeStringField model targetScope)
    (input : CheckedDocument model) (environment : Env) :
    Except AddressedTimeConstructionFault TimeConstructionComponent := do
  let path ← environment.pathForScope checked.declaration.repeatableScope
    |>.mapError (.sourceEnvironment checked.source.id)
  let cell ← input.read { field := checked.source.id, path }
    |>.mapError (fun cause => .component (.document cause))
  CheckedTimeStringField.classifyTimeStringComponent checked.source.id
    (observeCell .computation cell) |>.mapError .component

end CheckedAddressedTimeStringField

namespace CheckedAddressedTimeExtractorField

def read (checked : CheckedAddressedTimeExtractorField model targetScope)
    (input : CheckedDocument model) (environment : Env) :
    Except AddressedTimeConstructionFault TimeConstructionComponent := do
  let path ← environment.pathForScope checked.declaration.repeatableScope
    |>.mapError (.sourceEnvironment checked.source.id)
  let cell ← input.read { field := checked.source.id, path }
    |>.mapError (fun cause => .component (.document cause))
  CheckedTimeExtractorField.classifyTimeExtractorComponent checked.source.id
    checked.source.kind checked.part (observeCell .computation cell)
      |>.mapError .component

end CheckedAddressedTimeExtractorField

namespace CheckedAddressedTimeComponent

def read (checked : CheckedAddressedTimeComponent model targetScope)
    (input : CheckedDocument model) (environment : Env) :
    Except AddressedTimeConstructionFault TimeConstructionComponent :=
  match checked with
  | .constant value => pure (.value value)
  | .number field => field.read input environment
  | .string field => field.read input environment
  | .extractor field => field.read input environment

end CheckedAddressedTimeComponent

namespace CheckedAddressedTimeComponents

def evaluate (checked : CheckedAddressedTimeComponents model targetScope)
    (input : CheckedDocument model) (environment : Env) :
    Except AddressedTimeConstructionFault TimeConstructionResult :=
  checked.evaluateWith fun component => component.read input environment

end CheckedAddressedTimeComponents

namespace CheckedAddressedTimeConstructionComputation

/-- Exact authored-order field dependencies for scheduling and analysis. Constants contribute no edge. -/
def fieldDependencies
    (operation : CheckedAddressedTimeConstructionComputation model) :
    List FieldId :=
  operation.components.fieldDependencies

/-- Whether the addressed constructor reads one exact field declaration. -/
def referencesField
    (operation : CheckedAddressedTimeConstructionComputation model)
    (field : FieldId) : Bool :=
  operation.components.referencesField field

def evaluateOutcome
    (operation : CheckedAddressedTimeConstructionComputation model)
    (input : CheckedDocument model) (environment : Env) :
    Except AddressedTimeConstructionFault TimeTargetOutcome := do
  let result ← operation.components.evaluate input environment
  pure (operation.target.evaluate result.asTimeComputationResult)

private def evaluateAt
    (operation : CheckedAddressedTimeConstructionComputation model)
    (input : CheckedDocument model) (environment : Env) :
    Except AddressedTimeConstructionFault AddressedTimeConstructionOutcome := do
  let path ← environment.pathForScope
    operation.checkedTarget.declaration.repeatableScope
      |>.mapError .targetEnvironment
  let outcome ← operation.evaluateOutcome input environment
  pure {
    targetField := { field := operation.checkedTarget.targetField, path }
    outcome }

/-- Execute the checked construction once at every physical target row in document order. Each field component reads at its own bound scope inside that row. -/
def execute
    (operation : CheckedAddressedTimeConstructionComputation model)
    (input : CheckedDocument model) :
    Except AddressedTimeConstructionFault
      (List AddressedTimeConstructionOutcome) := do
  let environments ← input.actualRowEnvironments
    operation.checkedTarget.declaration.repeatableScope
      |>.mapError .targetRows
  environments.mapM (operation.evaluateAt input)

/-- Classify exact row outcomes by ordinary immutable-source clock equality. The scalar constructor's always-changed exception does not cross this repeatable boundary. -/
def executeResult
    (operation : CheckedAddressedTimeConstructionComputation model)
    (input : CheckedDocument model) (residualMessages : List ResidualMessage) :
    Except AddressedTimeConstructionFault
      (AddressedTimeConstructionRunView model ResidualMessage) := do
  let outcomes ← operation.execute input
  pure {
    operation
    time := TimeComputationRunView.fromOutcomesAt
      input.sourceTimeTargetStateAt residualMessages
      (outcomes.map fun entry => (entry.targetField, entry.outcome)) }

end CheckedAddressedTimeConstructionComputation

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

namespace AddressedTimeConstructionRunView

/-- Apply only retained row-local changes to a separate same-model destination projection. -/
def applyToChecked
    (view : AddressedTimeConstructionRunView model ResidualMessage)
    (destination : CheckedDocument model) :
    Except (TemporalValueComputationApplicationError CellAddr)
      (TimeComputationDestination CellAddr) :=
  view.time.applyTo destination.sourceTimeTargetStateAt

end AddressedTimeConstructionRunView

end A12Kernel
