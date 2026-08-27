import A12Kernel.Elaboration.TimeFirstFilledComputation
import A12Kernel.Elaboration.AddressedFirstFilledStar

/-! # Exact-address repeatable Time `FirstFilledValue`

This capsule binds one repeatable whole-second Time target to a sibling one-axis starred Time source. Every target row supplies the shared outer prefix, selection stays parent-local in the clock domain, and result classification retains Time's source-identical changed-action rule under exact cell addresses. Application remains a target-state projection and does not reconstruct a document or run validation.
-/

namespace A12Kernel

inductive AddressedTimeFirstFilledComputationElabError where
  | target (cause : ResolveError)
  | targetOutsideDeclaringGroup (path declaringGroup : GroupPath)
  | targetNotRepeatable (path : List String)
  | targetPolicy (cause : TimeTargetElabError)
  | source (cause : StarPathElabError)
  | sourceCarrier (path : List String)
  | sourceShape (path : List String)
  | sourceScope (path : List String)
  | targetSelfReference (field : FieldId)
  deriving Repr, DecidableEq

/-- One repeatable whole-second Time target and sibling Time star tied to the same checked model. -/
structure CheckedAddressedTimeFirstFilledComputation (model : FlatModel) where
  private mk ::
  checkedTarget : CheckedAddressedFirstFilledTarget model
  targetPolicy : CheckedTimeTarget model
  checkedSource : CheckedStarFieldPath model
  sourceCarrier :
    checkedSource.declaration.temporalFirstFilledStarCarrier? =
      some .timeHms
  placement : CheckedAddressedFirstFilledStarPlacement model
    checkedTarget checkedSource

namespace CheckedAddressedTimeFirstFilledComputation

def targetField
    (operation : CheckedAddressedTimeFirstFilledComputation model) : FieldId :=
  operation.checkedTarget.targetField

def target
    (operation : CheckedAddressedTimeFirstFilledComputation model) :
    FlatFieldDecl :=
  operation.checkedTarget.declaration

def source
    (operation : CheckedAddressedTimeFirstFilledComputation model) :
    CheckedStarFieldPath model :=
  operation.checkedSource

end CheckedAddressedTimeFirstFilledComputation

private def mapAddressedTimeTargetError :
    AddressedFirstFilledTargetElabError →
      AddressedTimeFirstFilledComputationElabError
  | .target cause => .target cause
  | .targetOutsideDeclaringGroup path declaringGroup =>
      .targetOutsideDeclaringGroup path declaringGroup
  | .targetNotRepeatable path => .targetNotRepeatable path

private def mapAddressedTimePlacementError :
    AddressedFirstFilledStarPlacementElabError →
      AddressedTimeFirstFilledComputationElabError
  | .sourceShape path => .sourceShape path
  | .sourceScope path => .sourceScope path
  | .targetSelfReference field => .targetSelfReference field

/-- Check repeatable target placement, exact whole-second Time policies, and sibling-star placement. -/
def checkAddressedTimeFirstFilledComputation
    (model : FlatModel) (declaringGroup : GroupPath) (targetField : FieldId)
    (authored : SurfaceStarFieldPath) :
    Except AddressedTimeFirstFilledComputationElabError
      (CheckedAddressedTimeFirstFilledComputation model) := do
  let target ← checkAddressedFirstFilledTarget model declaringGroup targetField
    |>.mapError mapAddressedTimeTargetError
  let targetPolicy ← elaborateTimeTargetIn model
      target.declaration.repeatableScope targetField
    |>.mapError .targetPolicy
  let source ← elaborateStarFieldPath model declaringGroup authored
    |>.mapError .source
  if hSource : source.declaration.temporalFirstFilledStarCarrier? =
      some .timeHms then
    let placement ← checkAddressedFirstFilledStarPlacement target source
      |>.mapError mapAddressedTimePlacementError
    pure {
      checkedTarget := target
      targetPolicy
      checkedSource := source
      sourceCarrier := hSource
      placement
    }
  else
    throw (.sourceCarrier source.declaration.path)

inductive AddressedTimeFirstFilledComputationFault where
  | targetRows (cause : ActualRowEnvironmentError)
  | targetEnvironment (cause : EnvBindingError)
  | source (cause : CheckedAddressingError)
  deriving Repr, DecidableEq

/-- One sibling-local Time selection retained under its exact target address. -/
structure AddressedTimeFirstFilledComputationOutcome where
  targetField : CellAddr
  outcome : TimeTargetOutcome
  deriving Repr, DecidableEq

/-- One checked addressed Time result backed by the common Time channels over exact cell addresses. -/
structure AddressedTimeFirstFilledComputationRunView (model : FlatModel)
    (ResidualMessage : Type) where
  private mk ::
  operation : CheckedAddressedTimeFirstFilledComputation model
  time : TimeComputationRunView ResidualMessage CellAddr

namespace CheckedAddressedTimeFirstFilledComputation

private def evaluateAt
    (operation : CheckedAddressedTimeFirstFilledComputation model)
    (input : CheckedDocument model) (environment : Env) :
    Except AddressedTimeFirstFilledComputationFault
      AddressedTimeFirstFilledComputationOutcome := do
  let targetPath ←
    environment.pathForScope operation.target.repeatableScope
      |>.mapError .targetEnvironment
  let resolved ← operation.source.resolveCheckedField input environment
    |>.mapError .source
  pure {
    targetField := { field := operation.targetField, path := targetPath }
    outcome := operation.targetPolicy.evaluate
      (evalTimeFirstFilledCells resolved.cells)
  }

/-- Execute one sibling-correlated Time scan per physical target row in document order. -/
def execute
    (operation : CheckedAddressedTimeFirstFilledComputation model)
    (input : CheckedDocument model) :
    Except AddressedTimeFirstFilledComputationFault
      (List AddressedTimeFirstFilledComputationOutcome) := do
  let environments ← input.actualRowEnvironments operation.target.repeatableScope
    |>.mapError .targetRows
  environments.mapM (operation.evaluateAt input)

/-- Classify every exact row outcome against immutable source target state through the shared Time result owner. -/
def executeResult
    (operation : CheckedAddressedTimeFirstFilledComputation model)
    (input : CheckedDocument model) (residualMessages : List ResidualMessage) :
    Except AddressedTimeFirstFilledComputationFault
      (AddressedTimeFirstFilledComputationRunView model ResidualMessage) := do
  let outcomes ← operation.execute input
  pure {
    operation
    time := TimeComputationRunView.fromOutcomesAt
      input.sourceTimeTargetStateAt residualMessages
      (outcomes.map fun entry => (entry.targetField, entry.outcome))
  }

end CheckedAddressedTimeFirstFilledComputation

namespace AddressedTimeFirstFilledComputationRunView

/-- Apply retained source-relative actions to exact Time cell-state projections from a separate checked document of the same model. -/
def applyToChecked
    (view : AddressedTimeFirstFilledComputationRunView model ResidualMessage)
    (destination : CheckedDocument model) :
    Except (TemporalValueComputationApplicationError CellAddr)
      (TimeComputationDestination CellAddr) :=
  view.time.applyTo destination.sourceTimeTargetStateAt

end AddressedTimeFirstFilledComputationRunView

end A12Kernel
