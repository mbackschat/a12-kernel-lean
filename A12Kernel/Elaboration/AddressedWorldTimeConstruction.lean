import A12Kernel.Elaboration.TimeComputation

/-! # World-backed repeatable `Time(...)` construction

This capsule composes the existing target-bound Time components with the existing dynamic
`Now` extractor inside one repeatable prefix. It retains authored dependency order, reads
addressed sources at their own bound scopes, takes `World` explicitly, executes physical
target rows only, and delegates result and application to the established addressed Time
boundary. Other nested temporal sources and external repeatable calibration remain separate.
-/

namespace A12Kernel

/-- One repeatable component input that is either target-bound document state or a nested dynamic `Now` extractor. -/
inductive SurfaceAddressedWorldTimeComponent where
  | addressed (source : SurfaceAddressedTimeComponent)
  | shiftedNowLiteral (part : TimeNumericPart)
      (unit : DateTimeSubdayUnit) (amount : Rat)
  | shiftedNowExpression (amountGroup : GroupPath) (part : TimeNumericPart)
      (unit : DateTimeSubdayUnit)
      (amount : AuthoredNumericExpr SurfaceNumericAtom)
  | shiftedNowRowExpression (part : TimeNumericPart)
      (unit : DateTimeSubdayUnit)
      (amount : AuthoredNumericExpr SurfaceNumericAtom)
  deriving Repr, DecidableEq

/-- A zero-through-three repeatable prefix that may mix addressed and world-dependent components. -/
abbrev SurfaceAddressedWorldTimeComponents :=
  TimeComponentPrefix SurfaceAddressedWorldTimeComponent

/-- One checked repeatable component that retains either its target-bound source or explicit world dependency. -/
inductive CheckedAddressedWorldTimeComponent (model : FlatModel)
    (targetScope : List RepeatableLevel) where
  | addressed (checked : CheckedAddressedTimeComponent model targetScope)
  | world (checked : CheckedWorldTimeComponent model)
  | rowWorld (checked : CheckedNowShiftedTimeExtractor model)

abbrev CheckedAddressedWorldTimeComponents (model : FlatModel)
    (targetScope : List RepeatableLevel) :=
  TimeComponentPrefix (CheckedAddressedWorldTimeComponent model targetScope)

namespace CheckedAddressedWorldTimeComponent

def referencesField
    (component : CheckedAddressedWorldTimeComponent model targetScope)
    (field : FieldId) : Bool :=
  match component with
  | .addressed checked => checked.referencesField field
  | .world checked => checked.referencesField field
  | .rowWorld checked => checked.source.amount.referencesField field

def fieldDependencies :
    CheckedAddressedWorldTimeComponent model targetScope → List FieldId
  | .addressed checked => checked.fieldDependencies
  | .world checked => checked.fieldDependencies
  | .rowWorld checked => checked.source.amount.fieldDependencies

private def readAddressedNowShifted
    (checked : CheckedNowShiftedTimeExtractor model)
    (world : World) (input : CheckedDocument model) (environment : Env) :
    Except AddressedTimeConstructionFault TimeConstructionComponent := do
  let amount ← checked.source.amount.readAddressed .computation {
      scalar := {
        fields := input.flatContext.withWorld world
        groups := GroupPresenceContext.unavailable
      }
      outer := environment
      input := .checked input
    } |>.mapError .amountAddressing
  let shifted ← ValueAsDateTimeResult.ofShiftedArithmetic checked.source.profile
    checked.source.unit world.now amount
      |>.mapError (fun cause => .component (.shifted cause))
  pure (ValueAsDateTimeTimeOperand.extractComponent
    shifted.asTimeOperand checked.part)

def read (checked : CheckedAddressedWorldTimeComponent model targetScope)
    (world : World) (input : CheckedDocument model) (environment : Env) :
    Except AddressedTimeConstructionFault TimeConstructionComponent :=
  match checked with
  | .addressed component => component.read input environment
  | .world component =>
      component.read .computation world input |>.mapError .component
  | .rowWorld component =>
      readAddressedNowShifted component world input environment

end CheckedAddressedWorldTimeComponent

namespace CheckedAddressedWorldTimeComponents

def referencesField
    (components : CheckedAddressedWorldTimeComponents model targetScope)
    (field : FieldId) : Bool :=
  components.referencesFieldWith
    CheckedAddressedWorldTimeComponent.referencesField field

def fieldDependencies :
    CheckedAddressedWorldTimeComponents model targetScope → List FieldId
  | .empty => []
  | .hour hour => hour.fieldDependencies
  | .minute hour minute => hour.fieldDependencies ++ minute.fieldDependencies
  | .second hour minute second =>
      hour.fieldDependencies ++ minute.fieldDependencies ++ second.fieldDependencies

def evaluate (checked : CheckedAddressedWorldTimeComponents model targetScope)
    (world : World) (input : CheckedDocument model) (environment : Env) :
    Except AddressedTimeConstructionFault TimeConstructionResult :=
  checked.evaluateWith fun component => component.read world input environment

end CheckedAddressedWorldTimeComponents

inductive AddressedWorldTimeConstructionComponentElabError where
  | addressed (cause : AddressedTimeConstructionComponentElabError)
  | shifted (cause : TimeComponentsElabError)
  | targetSelfReference (field : FieldId)
  deriving Repr, DecidableEq

inductive AddressedWorldTimeConstructionElabError where
  | target (cause : AddressedRepeatableTargetElabError)
  | targetPolicy (cause : TimeTargetElabError)
  | component (cause : AddressedWorldTimeConstructionComponentElabError)
  deriving Repr, DecidableEq

private def checkComponent
    (model : FlatModel) (declaringGroup : GroupPath)
    (targetField : FieldId) (targetScope : List RepeatableLevel)
    (targetPath : List String) (position : TimeComponentPosition) :
    SurfaceAddressedWorldTimeComponent →
      Except AddressedWorldTimeConstructionComponentElabError
        (CheckedAddressedWorldTimeComponent model targetScope)
  | .addressed source =>
      .addressed <$> (checkAddressedTimeComponent model declaringGroup targetField
        targetScope targetPath position source |>.mapError .addressed)
  | .shiftedNowLiteral part unit amount => do
      let checked ← elaborateNowShiftedTimeExtractorLiteral model position part
        unit amount |>.mapError .shifted
      pure (.world checked)
  | .shiftedNowExpression amountGroup part unit amount => do
      let checked ← elaborateNowShiftedTimeExtractorExpression model amountGroup
        position part unit amount |>.mapError .shifted
      pure (.world checked)
  | .shiftedNowRowExpression part unit amount => do
      let checkedAmount ←
        elaborateValueAsDateTimeRepeatableExpressionShiftAmount
          model declaringGroup amount
          |>.mapError (fun cause => .shifted (.shifted cause))
      let checked ← elaborateCheckedNowShiftedTimeExtractor model position
        part unit checkedAmount |>.mapError .shifted
      pure (.rowWorld checked)

private def checkComponents
    (model : FlatModel) (declaringGroup : GroupPath)
    (targetField : FieldId) (targetScope : List RepeatableLevel)
    (targetPath : List String) : SurfaceAddressedWorldTimeComponents →
      Except AddressedWorldTimeConstructionComponentElabError
        (CheckedAddressedWorldTimeComponents model targetScope)
  | .empty => pure .empty
  | .hour hour =>
      .hour <$> checkComponent model declaringGroup targetField
        targetScope targetPath .hour hour
  | .minute hour minute =>
      .minute <$> checkComponent model declaringGroup targetField
        targetScope targetPath .hour hour <*>
        checkComponent model declaringGroup targetField
          targetScope targetPath .minute minute
  | .second hour minute second =>
      .second <$> checkComponent model declaringGroup targetField
        targetScope targetPath .hour hour <*>
        checkComponent model declaringGroup targetField
          targetScope targetPath .minute minute <*>
        checkComponent model declaringGroup targetField
          targetScope targetPath .second second

/-- One repeatable complete-Time target and a checked addressed/world component prefix. -/
structure CheckedAddressedWorldTimeConstructionComputation
    (model : FlatModel) where
  private mk ::
  checkedTarget : CheckedAddressedRepeatableTarget model
  target : CheckedTimeTarget model
  components : CheckedAddressedWorldTimeComponents model
    checkedTarget.declaration.repeatableScope
  targetNotReferenced :
    components.referencesField checkedTarget.targetField = false

/-- Check repeatable target placement and a mixed addressed/world component prefix without sampling the world. -/
def checkAddressedWorldTimeConstructionComputation
    (model : FlatModel) (declaringGroup : GroupPath) (targetField : FieldId)
    (authored : SurfaceAddressedWorldTimeComponents) :
    Except AddressedWorldTimeConstructionElabError
      (CheckedAddressedWorldTimeConstructionComputation model) := do
  let checkedTarget ← checkAddressedRepeatableTarget model declaringGroup targetField
    |>.mapError .target
  let target ← elaborateTimeTargetIn model
    checkedTarget.declaration.repeatableScope targetField
      |>.mapError .targetPolicy
  let components ← checkComponents model declaringGroup targetField
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

structure AddressedWorldTimeConstructionRunView (model : FlatModel)
    (ResidualMessage : Type) where
  private mk ::
  operation : CheckedAddressedWorldTimeConstructionComputation model
  time : TimeComputationRunView ResidualMessage CellAddr

namespace CheckedAddressedWorldTimeConstructionComputation

/-- Exact authored-order field dependencies, including direct Number atoms inside the dynamic shift amount. -/
def fieldDependencies
    (operation : CheckedAddressedWorldTimeConstructionComputation model) :
    List FieldId :=
  operation.components.fieldDependencies

def referencesField
    (operation : CheckedAddressedWorldTimeConstructionComputation model)
    (field : FieldId) : Bool :=
  operation.components.referencesField field

def evaluateOutcome
    (operation : CheckedAddressedWorldTimeConstructionComputation model)
    (world : World) (input : CheckedDocument model) (environment : Env) :
    Except AddressedTimeConstructionFault TimeTargetOutcome := do
  let result ← operation.components.evaluate world input environment
  pure (operation.target.evaluate result.asTimeComputationResult)

private def evaluateAt
    (operation : CheckedAddressedWorldTimeConstructionComputation model)
    (world : World) (input : CheckedDocument model) (environment : Env) :
    Except AddressedTimeConstructionFault AddressedTimeConstructionOutcome := do
  let path ← environment.pathForScope
    operation.checkedTarget.declaration.repeatableScope
      |>.mapError .targetEnvironment
  let outcome ← operation.evaluateOutcome world input environment
  pure {
    targetField := { field := operation.checkedTarget.targetField, path }
    outcome }

/-- Execute once at every physical target row. No row means no world-dependent component or amount read. -/
def execute
    (operation : CheckedAddressedWorldTimeConstructionComputation model)
    (world : World) (input : CheckedDocument model) :
    Except AddressedTimeConstructionFault
      (List AddressedTimeConstructionOutcome) := do
  let environments ← input.actualRowEnvironments
    operation.checkedTarget.declaration.repeatableScope
      |>.mapError .targetRows
  environments.mapM (operation.evaluateAt world input)

/-- Classify world-aware row outcomes through the same source-relative Time result boundary. -/
def executeResult
    (operation : CheckedAddressedWorldTimeConstructionComputation model)
    (world : World) (input : CheckedDocument model)
    (residualMessages : List ResidualMessage) :
    Except AddressedTimeConstructionFault
      (AddressedWorldTimeConstructionRunView model ResidualMessage) := do
  let outcomes ← operation.execute world input
  pure {
    operation
    time := TimeComputationRunView.fromOutcomesAt
      input.sourceTimeTargetStateAt residualMessages
      (outcomes.map fun entry => (entry.targetField, entry.outcome)) }

end CheckedAddressedWorldTimeConstructionComputation

namespace AddressedWorldTimeConstructionRunView

/-- Apply only retained row-local changes to a separate same-model destination projection. -/
def applyToChecked
    (view : AddressedWorldTimeConstructionRunView model ResidualMessage)
    (destination : CheckedDocument model) :
    Except (TemporalValueComputationApplicationError CellAddr)
      (TimeComputationDestination CellAddr) :=
  view.time.applyTo destination.sourceTimeTargetStateAt

end AddressedWorldTimeConstructionRunView

end A12Kernel
