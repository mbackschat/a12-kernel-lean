import A12Kernel.Elaboration.BooleanFirstFilledComputation
import A12Kernel.Elaboration.AddressedFirstFilledStar

/-! # Exact-address repeatable Boolean `FirstFilledValue`

This capsule binds one repeatable Boolean target to a one-axis starred Boolean source with a nonempty outer binding prefix. Those levels are supplied by each physical target environment, so a sibling source extent stays correlated to its enclosing row. Result classification and application reuse the typed Boolean channels without reconstructing a document or running validation.
-/

namespace A12Kernel

inductive AddressedBooleanFirstFilledComputationElabError where
  | target (cause : ResolveError)
  | targetOutsideDeclaringGroup (path declaringGroup : GroupPath)
  | targetNotRepeatable (path : List String)
  | targetKind (path : List String) (actual : SurfaceScalarKind)
  | source (cause : StarPathElabError)
  | sourceKind (path : List String) (actual : SurfaceScalarKind)
  | sourceShape (path : List String)
  | sourceScope (path : List String)
  | targetSelfReference (field : FieldId)
  deriving Repr, DecidableEq

/-- One repeatable Boolean target and one checked single-reopened-axis Boolean source tied to the same validated model. -/
structure CheckedAddressedBooleanFirstFilledComputation (model : FlatModel) where
  private mk ::
  checkedTarget : CheckedAddressedFirstFilledTarget model
  checkedSource : CheckedStarFieldPath model
  placement : CheckedAddressedFirstFilledStarPlacement model
    checkedTarget checkedSource
  targetBoolean : checkedTarget.declaration.policy.kind = .boolean
  sourceBoolean : checkedSource.declaration.policy.kind = .boolean

namespace CheckedAddressedBooleanFirstFilledComputation

def declaringGroup
    (operation : CheckedAddressedBooleanFirstFilledComputation model) : GroupPath :=
  operation.checkedTarget.declaringGroup

def targetField
    (operation : CheckedAddressedBooleanFirstFilledComputation model) : FieldId :=
  operation.checkedTarget.targetField

def target
    (operation : CheckedAddressedBooleanFirstFilledComputation model) : FlatFieldDecl :=
  operation.checkedTarget.declaration

def source
    (operation : CheckedAddressedBooleanFirstFilledComputation model) :
    CheckedStarFieldPath model :=
  operation.checkedSource

theorem targetOwned
    (operation : CheckedAddressedBooleanFirstFilledComputation model) :
    model.lookupUniqueId operation.targetField = .ok operation.target :=
  operation.checkedTarget.owned

/-- The target lies at or below its declaring group. This states containment only; which groups the
checker *refuses* is a separate question, since it also rejects an unrepresentable declaring group. -/
theorem targetContainedInDeclaringGroup
    (operation : CheckedAddressedBooleanFirstFilledComputation model) :
    GroupPath.isPrefixOf operation.declaringGroup operation.target.groupPath = true :=
  operation.checkedTarget.targetContained

theorem targetRepeatable
    (operation : CheckedAddressedBooleanFirstFilledComputation model) :
    operation.target.repeatableScope ≠ [] :=
  operation.checkedTarget.repeatable

theorem sourceSingleReopenedAxis
    (operation : CheckedAddressedBooleanFirstFilledComputation model) :
    operation.source.reopenedScope.length = 1 :=
  operation.placement.sourceSingleReopenedAxis

theorem sourceBindingBound
    (operation : CheckedAddressedBooleanFirstFilledComputation model) :
    operation.source.bindingScope.all operation.target.repeatableScope.contains = true :=
  operation.placement.sourceBindingBound

theorem sourceBindingNonempty
    (operation : CheckedAddressedBooleanFirstFilledComputation model) :
    operation.source.bindingScope ≠ [] :=
  operation.placement.sourceBindingNonempty

theorem targetNotReferenced
    (operation : CheckedAddressedBooleanFirstFilledComputation model) :
    operation.source.declaration.id ≠ operation.targetField :=
  operation.placement.targetNotReferenced

end CheckedAddressedBooleanFirstFilledComputation

private def mapAddressedBooleanTargetError :
    AddressedFirstFilledTargetElabError →
      AddressedBooleanFirstFilledComputationElabError
  | .target cause => .target cause
  | .targetOutsideDeclaringGroup path declaringGroup =>
      .targetOutsideDeclaringGroup path declaringGroup
  | .targetNotRepeatable path => .targetNotRepeatable path

private def mapAddressedBooleanStarPlacementError :
    AddressedFirstFilledStarPlacementElabError →
      AddressedBooleanFirstFilledComputationElabError
  | .sourceShape path => .sourceShape path
  | .sourceScope path => .sourceScope path
  | .targetSelfReference field => .targetSelfReference field

/-- Check the target first, then certify one Boolean star with a nonempty outer binding scope available at every target row. -/
def checkAddressedBooleanFirstFilledComputation
    (model : FlatModel) (declaringGroup : GroupPath) (targetField : FieldId)
    (authored : SurfaceStarFieldPath) :
    Except AddressedBooleanFirstFilledComputationElabError
      (CheckedAddressedBooleanFirstFilledComputation model) :=
  do
    let target ← checkAddressedFirstFilledTarget model declaringGroup targetField
      |>.mapError mapAddressedBooleanTargetError
    if hTargetKind : target.declaration.policy.kind = .boolean then
      let source ← elaborateStarFieldPath model declaringGroup authored
        |>.mapError .source
      if hSourceKind : source.declaration.policy.kind = .boolean then
        let placement ← checkAddressedFirstFilledStarPlacement target source
          |>.mapError mapAddressedBooleanStarPlacementError
        pure {
          checkedTarget := target
          checkedSource := source
          placement
          targetBoolean := hTargetKind
          sourceBoolean := hSourceKind
        }
      else
        throw (.sourceKind source.declaration.path
          source.declaration.policy.kind.surfaceKind)
    else
      throw (.targetKind target.declaration.path
        target.declaration.policy.kind.surfaceKind)

inductive AddressedBooleanFirstFilledComputationFault where
  | targetRows (cause : ActualRowEnvironmentError)
  | targetEnvironment (cause : EnvBindingError)
  | source (cause : CheckedAddressingError)
  deriving Repr, DecidableEq

/-- One row-local Boolean selection retained under its exact target address. -/
structure AddressedBooleanFirstFilledComputationOutcome where
  targetField : CellAddr
  result : FirstFilledBooleanComputationResult
  deriving Repr, DecidableEq

/-- One checked addressed Boolean result backed by the shared typed Boolean channels. -/
structure AddressedBooleanFirstFilledComputationRunView (model : FlatModel)
    (ResidualMessage : Type) where
  private mk ::
  operation : CheckedAddressedBooleanFirstFilledComputation model
  boolean : BooleanComputationRunView ResidualMessage CellAddr

namespace CheckedAddressedBooleanFirstFilledComputation

private def evaluateAtWithRead
    (operation : CheckedAddressedBooleanFirstFilledComputation model)
    (input : CheckedDocument model)
    (read : CellAddr → Except CheckedDocumentError CheckedCell)
    (environment : Env) :
    Except AddressedBooleanFirstFilledComputationFault
      AddressedBooleanFirstFilledComputationOutcome := do
  let targetPath ←
    environment.pathForScope operation.target.repeatableScope
      |>.mapError .targetEnvironment
  let resolved ← operation.source.resolveCheckedFieldWithRead input read environment
    |>.mapError .source
  pure {
    targetField := { field := operation.targetField, path := targetPath }
    result := evalFirstFilledBoolean
      (resolved.cells.map fun cell => booleanFirstFilledCellAt cell.cell)
  }

/-- The no-value outcome an over-limit target row takes instead of a scan, retaining its exact
address so the application projection clears it. -/
def clearedAt (operation : CheckedAddressedBooleanFirstFilledComputation model)
    (environment : Env) :
    Except AddressedBooleanFirstFilledComputationFault
      AddressedBooleanFirstFilledComputationOutcome := do
  let targetPath ←
    environment.pathForScope operation.target.repeatableScope
      |>.mapError .targetEnvironment
  pure {
    targetField := { field := operation.targetField, path := targetPath }
    result := .noValue
  }

/-- Execute one sibling-correlated first-filled scan per **in-capacity** target row through a caller-supplied exact-address source view, and only a clear at each over-limit row. Target topology and immutable source target state remain unchanged. -/
def executeWithRead
    (operation : CheckedAddressedBooleanFirstFilledComputation model)
    (input : CheckedDocument model)
    (read : CellAddr → Except CheckedDocumentError CheckedCell) :
    Except AddressedBooleanFirstFilledComputationFault
      (List AddressedBooleanFirstFilledComputationOutcome) := do
  input.computationRowOutcomes operation.target.repeatableScope .targetRows
    operation.clearedAt (operation.evaluateAtWithRead input read)

/-- Execute one sibling-correlated first-filled scan per in-capacity target row in document order, and a clear at each over-limit row. -/
def execute
    (operation : CheckedAddressedBooleanFirstFilledComputation model)
    (input : CheckedDocument model) :
    Except AddressedBooleanFirstFilledComputationFault
      (List AddressedBooleanFirstFilledComputationOutcome) :=
  operation.executeWithRead input input.read

/-- Classify caller-view outcomes against immutable source target state through the shared Boolean result owner. -/
def executeResultWithRead
    (operation : CheckedAddressedBooleanFirstFilledComputation model)
    (input : CheckedDocument model)
    (read : CellAddr → Except CheckedDocumentError CheckedCell)
    (residualMessages : List ResidualMessage) :
    Except AddressedBooleanFirstFilledComputationFault
      (AddressedBooleanFirstFilledComputationRunView model ResidualMessage) := do
  let outcomes ← operation.executeWithRead input read
  pure {
    operation
    boolean := BooleanComputationRunView.fromSourcedOutcomes residualMessages
      (outcomes.map fun entry =>
        (entry.targetField, entry.result,
          input.sourceBooleanTargetStateAt entry.targetField))
  }

/-- Classify every exact row outcome against immutable source target state through the shared Boolean result owner. -/
def executeResult
    (operation : CheckedAddressedBooleanFirstFilledComputation model)
    (input : CheckedDocument model) (residualMessages : List ResidualMessage) :
    Except AddressedBooleanFirstFilledComputationFault
      (AddressedBooleanFirstFilledComputationRunView model ResidualMessage) :=
  operation.executeResultWithRead input input.read residualMessages

end CheckedAddressedBooleanFirstFilledComputation

namespace AddressedBooleanFirstFilledComputationRunView

/-- Apply only retained exact-address Boolean actions to a separate same-model destination projection. -/
def applyToChecked
    (view : AddressedBooleanFirstFilledComputationRunView model ResidualMessage)
    (destination : CheckedDocument model) :
    BooleanComputationDestination CellAddr :=
  view.boolean.applyTo destination.sourceBooleanTargetStateAt

end AddressedBooleanFirstFilledComputationRunView

end A12Kernel
