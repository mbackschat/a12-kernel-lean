import A12Kernel.Elaboration.DateTimeFirstFilledComputation
import A12Kernel.Elaboration.AddressedFirstFilledStar

/-! # Exact-address repeatable DateTime `FirstFilledValue`

This capsule binds one repeatable complete DateTime target to a sibling one-axis starred DateTime source. Every target row supplies the shared outer prefix, selection stays parent-local in the exact-instant domain, and target rendering uses the checked model-zone profile. Result classification and application retain exact cell addresses without reconstructing a document or running validation.
-/

namespace A12Kernel

inductive AddressedDateTimeFirstFilledComputationElabError where
  | target (cause : ResolveError)
  | targetOutsideDeclaringGroup (path declaringGroup : GroupPath)
  | targetNotRepeatable (path : List String)
  | targetPolicy (cause : DateTimeTargetElabError)
  | source (cause : StarPathElabError)
  | sourceCarrier (path : List String)
  | sourceShape (path : List String)
  | sourceScope (path : List String)
  | targetSelfReference (field : FieldId)
  deriving Repr, DecidableEq

/-- One repeatable complete DateTime target and one sibling complete DateTime star tied to the same checked model. -/
structure CheckedAddressedDateTimeFirstFilledComputation (model : FlatModel) where
  private mk ::
  checkedTarget : CheckedAddressedFirstFilledTarget model
  targetPolicy : CheckedDateTimeTarget model
  checkedSource : CheckedStarFieldPath model
  sourceCarrier :
    checkedSource.declaration.temporalFirstFilledStarCarrier? =
      some .dateTimeIso
  placement : CheckedAddressedFirstFilledStarPlacement model
    checkedTarget checkedSource

namespace CheckedAddressedDateTimeFirstFilledComputation

def declaringGroup
    (operation : CheckedAddressedDateTimeFirstFilledComputation model) :
    GroupPath :=
  operation.checkedTarget.declaringGroup

def targetField
    (operation : CheckedAddressedDateTimeFirstFilledComputation model) :
    FieldId :=
  operation.checkedTarget.targetField

def target
    (operation : CheckedAddressedDateTimeFirstFilledComputation model) :
    FlatFieldDecl :=
  operation.checkedTarget.declaration

def source
    (operation : CheckedAddressedDateTimeFirstFilledComputation model) :
    CheckedStarFieldPath model :=
  operation.checkedSource

end CheckedAddressedDateTimeFirstFilledComputation

private def mapAddressedDateTimeTargetError :
    AddressedFirstFilledTargetElabError →
      AddressedDateTimeFirstFilledComputationElabError
  | .target cause => .target cause
  | .targetOutsideDeclaringGroup path declaringGroup =>
      .targetOutsideDeclaringGroup path declaringGroup
  | .targetNotRepeatable path => .targetNotRepeatable path

private def mapAddressedDateTimePlacementError :
    AddressedFirstFilledStarPlacementElabError →
      AddressedDateTimeFirstFilledComputationElabError
  | .sourceShape path => .sourceShape path
  | .sourceScope path => .sourceScope path
  | .targetSelfReference field => .targetSelfReference field

/-- Check repeatable target placement, the complete target profile and model zone, the complete source carrier, and sibling-star placement. -/
def checkAddressedDateTimeFirstFilledComputation
    (model : FlatModel) (declaringGroup : GroupPath) (targetField : FieldId)
    (authored : SurfaceStarFieldPath) :
    Except AddressedDateTimeFirstFilledComputationElabError
      (CheckedAddressedDateTimeFirstFilledComputation model) := do
  let target ← checkAddressedFirstFilledTarget model declaringGroup targetField
    |>.mapError mapAddressedDateTimeTargetError
  let targetPolicy ← elaborateDateTimeTargetIn model
      target.declaration.repeatableScope targetField
    |>.mapError .targetPolicy
  let source ← elaborateStarFieldPath model declaringGroup authored
    |>.mapError .source
  if hSource : source.declaration.temporalFirstFilledStarCarrier? =
      some .dateTimeIso then
    let placement ← checkAddressedFirstFilledStarPlacement target source
      |>.mapError mapAddressedDateTimePlacementError
    pure {
      checkedTarget := target
      targetPolicy
      checkedSource := source
      sourceCarrier := hSource
      placement
    }
  else
    throw (.sourceCarrier source.declaration.path)

inductive AddressedDateTimeFirstFilledComputationFault where
  | targetRows (cause : ActualRowEnvironmentError)
  | targetEnvironment (cause : EnvBindingError)
  | source (cause : CheckedAddressingError)
  | target (cause : DateTimeTargetEvaluationFault)
  deriving Repr, DecidableEq

/-- One sibling-local DateTime selection retained under its exact target address. -/
structure AddressedDateTimeFirstFilledComputationOutcome where
  targetField : CellAddr
  outcome : DateTimeTargetOutcome
  deriving Repr, DecidableEq

/-- One checked addressed DateTime result backed by the common five DateTime channels over exact cell addresses. -/
structure AddressedDateTimeFirstFilledComputationRunView (model : FlatModel)
    (ResidualMessage : Type) where
  private mk ::
  operation : CheckedAddressedDateTimeFirstFilledComputation model
  dateTime : DateTimeComputationRunView ResidualMessage CellAddr

namespace CheckedAddressedDateTimeFirstFilledComputation

private def evaluateAt
    (operation : CheckedAddressedDateTimeFirstFilledComputation model)
    (input : CheckedDocument model) (environment : Env) :
    Except AddressedDateTimeFirstFilledComputationFault
      AddressedDateTimeFirstFilledComputationOutcome := do
  let targetPath ←
    environment.pathForScope operation.target.repeatableScope
      |>.mapError .targetEnvironment
  let resolved ← operation.source.resolveCheckedField input environment
    |>.mapError .source
  let outcome ← operation.targetPolicy.evaluate
      (evalDateTimeFirstFilledCells resolved.cells)
    |>.mapError .target
  pure {
    targetField := { field := operation.targetField, path := targetPath }
    outcome
  }

/-- Execute one sibling-correlated DateTime scan per physical target row in document order. -/
def execute
    (operation : CheckedAddressedDateTimeFirstFilledComputation model)
    (input : CheckedDocument model) :
    Except AddressedDateTimeFirstFilledComputationFault
      (List AddressedDateTimeFirstFilledComputationOutcome) := do
  let environments ← input.actualRowEnvironments operation.target.repeatableScope
    |>.mapError .targetRows
  environments.mapM (operation.evaluateAt input)

/-- Classify every exact row outcome against immutable source target state through the shared DateTime result owner. -/
def executeResult
    (operation : CheckedAddressedDateTimeFirstFilledComputation model)
    (input : CheckedDocument model) (residualMessages : List ResidualMessage) :
    Except AddressedDateTimeFirstFilledComputationFault
      (AddressedDateTimeFirstFilledComputationRunView model ResidualMessage) := do
  let outcomes ← operation.execute input
  pure {
    operation
    dateTime := DateTimeComputationRunView.fromOutcomesAt
      input.sourceDateTimeTargetStateAt residualMessages
      (outcomes.map fun entry => (entry.targetField, entry.outcome))
  }

end CheckedAddressedDateTimeFirstFilledComputation

namespace AddressedDateTimeFirstFilledComputationRunView

/-- Apply retained source-relative actions to exact DateTime cell-state projections from a separate checked document of the same model. -/
def applyToChecked
    (view : AddressedDateTimeFirstFilledComputationRunView model ResidualMessage)
    (destination : CheckedDocument model) :
    Except (DateTimeComputationRunView.DateTimeComputationRunApplicationError
      CellAddr) (DateTimeComputationDestination CellAddr) :=
  view.dateTime.applyTo destination.sourceDateTimeTargetStateAt

end AddressedDateTimeFirstFilledComputationRunView

end A12Kernel
