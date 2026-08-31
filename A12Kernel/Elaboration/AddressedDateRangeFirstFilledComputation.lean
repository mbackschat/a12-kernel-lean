import A12Kernel.Elaboration.DateRangeFirstFilledComputation
import A12Kernel.Elaboration.AddressedFirstFilledStar

/-! # Exact-address repeatable DateRange `FirstFilledValue`

This capsule binds one repeatable DateRange target to a sibling one-axis starred DateRange source. Each physical target environment supplies the shared outer prefix, the source scan stays parent-local, and the target's checked presentation renders every selected value. Result classification and application retain exact cell addresses without reconstructing a document or running validation.
-/

namespace A12Kernel

inductive AddressedDateRangeFirstFilledComputationElabError where
  | target (cause : ResolveError)
  | targetOutsideDeclaringGroup (path declaringGroup : GroupPath)
  | targetNotRepeatable (path : List String)
  | targetProfile (cause : CanonicalDateRangeFieldError)
  | source (cause : StarPathElabError)
  | sourceProfile (cause : CanonicalDateRangeFieldError)
  | sourceProfileNotComparable (target source : List String)
  | sourceShape (path : List String)
  | sourceScope (path : List String)
  | targetSelfReference (field : FieldId)
  deriving Repr, DecidableEq

/-- One repeatable DateRange target and one component-compatible sibling DateRange star tied to the same checked model. -/
structure CheckedAddressedDateRangeFirstFilledComputation (model : FlatModel) where
  private mk ::
  checkedTarget : CheckedAddressedFirstFilledTarget model
  targetProfile : CheckedDateRangeInputField
  checkedSource : CheckedStarFieldPath model
  sourceProfile : CheckedDateRangeInputField
  placement : CheckedAddressedFirstFilledStarPlacement model
    checkedTarget checkedSource
  sourceComparable :
    targetProfile.format.components = sourceProfile.format.components

namespace CheckedAddressedDateRangeFirstFilledComputation

def declaringGroup
    (operation : CheckedAddressedDateRangeFirstFilledComputation model) :
    GroupPath :=
  operation.checkedTarget.declaringGroup

def targetField
    (operation : CheckedAddressedDateRangeFirstFilledComputation model) :
    FieldId :=
  operation.checkedTarget.targetField

def target
    (operation : CheckedAddressedDateRangeFirstFilledComputation model) :
    FlatFieldDecl :=
  operation.checkedTarget.declaration

def source
    (operation : CheckedAddressedDateRangeFirstFilledComputation model) :
    CheckedStarFieldPath model :=
  operation.checkedSource

end CheckedAddressedDateRangeFirstFilledComputation

private def mapAddressedDateRangeTargetError :
    AddressedFirstFilledTargetElabError →
      AddressedDateRangeFirstFilledComputationElabError
  | .target cause => .target cause
  | .targetOutsideDeclaringGroup path declaringGroup =>
      .targetOutsideDeclaringGroup path declaringGroup
  | .targetNotRepeatable path => .targetNotRepeatable path

private def mapAddressedDateRangePlacementError :
    AddressedFirstFilledStarPlacementElabError →
      AddressedDateRangeFirstFilledComputationElabError
  | .sourceShape path => .sourceShape path
  | .sourceScope path => .sourceScope path
  | .targetSelfReference field => .targetSelfReference field

/-- Check target placement, both declaration-owned DateRange profiles, their component compatibility, and the shared sibling-star placement. -/
def checkAddressedDateRangeFirstFilledComputation
    (model : FlatModel) (declaringGroup : GroupPath) (targetField : FieldId)
    (authored : SurfaceStarFieldPath) :
    Except AddressedDateRangeFirstFilledComputationElabError
      (CheckedAddressedDateRangeFirstFilledComputation model) := do
  let target ← checkAddressedFirstFilledTarget model declaringGroup targetField
    |>.mapError mapAddressedDateRangeTargetError
  let targetProfile ← certifyDateRangeInputField target.declaration
    |>.mapError .targetProfile
  let source ← elaborateStarFieldPath model declaringGroup authored
    |>.mapError .source
  let sourceProfile ← certifyDateRangeInputField source.declaration
    |>.mapError .sourceProfile
  if hComparable :
      targetProfile.format.components = sourceProfile.format.components then
    let placement ← checkAddressedFirstFilledStarPlacement target source
      |>.mapError mapAddressedDateRangePlacementError
    pure {
      checkedTarget := target
      targetProfile
      checkedSource := source
      sourceProfile
      placement
      sourceComparable := hComparable
    }
  else
    throw (.sourceProfileNotComparable target.declaration.path
      source.declaration.path)

inductive AddressedDateRangeFirstFilledComputationFault where
  | targetRows (cause : ActualRowEnvironmentError)
  | targetEnvironment (cause : EnvBindingError)
  | source (cause : CheckedAddressingError)
  | unresolvedEndpoint (range : DateRangeValue)
  deriving Repr, DecidableEq

/-- One sibling-local DateRange selection retained under its exact target address. -/
structure AddressedDateRangeFirstFilledComputationOutcome where
  targetField : CellAddr
  outcome : DateRangeTargetOutcome
  deriving Repr, DecidableEq

/-- One checked addressed DateRange result backed by the common five DateRange channels over exact cell addresses. -/
structure AddressedDateRangeFirstFilledComputationRunView (model : FlatModel)
    (ResidualMessage : Type) where
  private mk ::
  operation : CheckedAddressedDateRangeFirstFilledComputation model
  dateRange : DateRangeComputationRunView ResidualMessage CellAddr

namespace CheckedAddressedDateRangeFirstFilledComputation

private def evaluateAtWithRead
    (operation : CheckedAddressedDateRangeFirstFilledComputation model)
    (input : CheckedDocument model)
    (read : CellAddr → Except CheckedDocumentError CheckedCell)
    (environment : Env) :
    Except AddressedDateRangeFirstFilledComputationFault
      AddressedDateRangeFirstFilledComputationOutcome := do
  let targetPath ←
    environment.pathForScope operation.target.repeatableScope
      |>.mapError .targetEnvironment
  let resolved ← operation.source.resolveCheckedFieldWithRead input read environment
    |>.mapError .source
  let outcome ← operation.targetProfile.format.evaluateComputationResult
      (evalDateRangeFirstFilledCells resolved.cells)
    |>.mapError fun
      | .unresolvedEndpoint value => .unresolvedEndpoint value
  pure {
    targetField := { field := operation.targetField, path := targetPath }
    outcome
  }

/-- Execute one sibling-correlated DateRange scan per physical target row through a caller-supplied exact-address view. Target-row ownership and source topology remain immutable. -/
def executeWithRead
    (operation : CheckedAddressedDateRangeFirstFilledComputation model)
    (input : CheckedDocument model)
    (read : CellAddr → Except CheckedDocumentError CheckedCell) :
    Except AddressedDateRangeFirstFilledComputationFault
      (List AddressedDateRangeFirstFilledComputationOutcome) := do
  let environments ← input.computationRowEnvironments operation.target.repeatableScope
    |>.mapError .targetRows
  environments.mapM (operation.evaluateAtWithRead input read)

/-- Execute one sibling-correlated DateRange scan per physical target row in document order. -/
def execute
    (operation : CheckedAddressedDateRangeFirstFilledComputation model)
    (input : CheckedDocument model) :
    Except AddressedDateRangeFirstFilledComputationFault
      (List AddressedDateRangeFirstFilledComputationOutcome) :=
  operation.executeWithRead input input.read

/-- Classify caller-view row outcomes against immutable source target state through the shared DateRange result owner. -/
def executeResultWithRead
    (operation : CheckedAddressedDateRangeFirstFilledComputation model)
    (input : CheckedDocument model)
    (read : CellAddr → Except CheckedDocumentError CheckedCell)
    (residualMessages : List ResidualMessage) :
    Except AddressedDateRangeFirstFilledComputationFault
      (AddressedDateRangeFirstFilledComputationRunView model ResidualMessage) := do
  let outcomes ← operation.executeWithRead input read
  pure {
    operation
    dateRange := DateRangeComputationRunView.fromOutcomesAt
      input.sourceDateRangeTargetStateAt residualMessages
      (outcomes.map fun entry => (entry.targetField, entry.outcome))
  }

/-- Classify every exact row outcome against immutable source target state through the shared DateRange result owner. -/
def executeResult
    (operation : CheckedAddressedDateRangeFirstFilledComputation model)
    (input : CheckedDocument model) (residualMessages : List ResidualMessage) :
    Except AddressedDateRangeFirstFilledComputationFault
      (AddressedDateRangeFirstFilledComputationRunView model ResidualMessage) :=
  operation.executeResultWithRead input input.read residualMessages

end CheckedAddressedDateRangeFirstFilledComputation

namespace AddressedDateRangeFirstFilledComputationRunView

/-- Apply retained source-relative actions to exact DateRange cell-state projections from a separate checked document of the same model. -/
def applyToChecked
    (view : AddressedDateRangeFirstFilledComputationRunView model ResidualMessage)
    (destination : CheckedDocument model) :
    Except (DateRangeComputationRunView.DateRangeComputationRunApplicationError
      CellAddr) (DateRangeComputationDestination CellAddr) :=
  view.dateRange.applyTo destination.sourceDateRangeTargetStateAt

end AddressedDateRangeFirstFilledComputationRunView

end A12Kernel
