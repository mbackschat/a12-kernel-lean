import A12Kernel.Elaboration.DateFragmentFirstFilledComputation
import A12Kernel.Elaboration.AddressedFirstFilledStar

/-! # Exact-address repeatable DateFragment `FirstFilledValue`

This capsule binds one repeatable DateFragment target to a sibling one-axis starred source with the same exact admitted fragment profile. Every physical target row supplies the shared outer prefix, selection stays parent-local, and the exact selected token is classified and applied under its target `CellAddr`. No document is reconstructed and no validation runs.
-/

namespace A12Kernel

inductive AddressedDateFragmentFirstFilledComputationElabError where
  | target (cause : ResolveError)
  | targetOutsideDeclaringGroup (path declaringGroup : GroupPath)
  | targetNotRepeatable (path : List String)
  | targetCarrier (path : List String)
  | source (cause : StarPathElabError)
  | sourceCarrier (path : List String)
      (expected : TemporalFirstFilledStarCarrier)
      (actual : Option TemporalFirstFilledStarCarrier)
  | sourceShape (path : List String)
  | sourceScope (path : List String)
  | targetSelfReference (field : FieldId)
  deriving Repr, DecidableEq

/-- One repeatable DateFragment target and sibling star carrying the same exact fragment profile. -/
structure CheckedAddressedDateFragmentFirstFilledComputation
    (model : FlatModel) where
  private mk ::
  checkedTarget : CheckedAddressedFirstFilledTarget model
  checkedSource : CheckedStarFieldPath model
  placement : CheckedAddressedFirstFilledStarPlacement model
    checkedTarget checkedSource
  carrier : TemporalFirstFilledStarCarrier
  carrierIsFragment : carrier.isDateFragment = true
  targetCarrier :
    checkedTarget.declaration.temporalFirstFilledStarCarrier? = some carrier
  sourceCarrier :
    checkedSource.declaration.temporalFirstFilledStarCarrier? = some carrier

namespace CheckedAddressedDateFragmentFirstFilledComputation

def targetField
    (operation : CheckedAddressedDateFragmentFirstFilledComputation model) :
    FieldId :=
  operation.checkedTarget.targetField

def target
    (operation : CheckedAddressedDateFragmentFirstFilledComputation model) :
    FlatFieldDecl :=
  operation.checkedTarget.declaration

def source
    (operation : CheckedAddressedDateFragmentFirstFilledComputation model) :
    CheckedStarFieldPath model :=
  operation.checkedSource

end CheckedAddressedDateFragmentFirstFilledComputation

private def mapAddressedDateFragmentTargetError :
    AddressedFirstFilledTargetElabError →
      AddressedDateFragmentFirstFilledComputationElabError
  | .target cause => .target cause
  | .targetOutsideDeclaringGroup path declaringGroup =>
      .targetOutsideDeclaringGroup path declaringGroup
  | .targetNotRepeatable path => .targetNotRepeatable path

private def mapAddressedDateFragmentPlacementError :
    AddressedFirstFilledStarPlacementElabError →
      AddressedDateFragmentFirstFilledComputationElabError
  | .sourceShape path => .sourceShape path
  | .sourceScope path => .sourceScope path
  | .targetSelfReference field => .targetSelfReference field

/-- Check repeatable target placement, one of the four exact DateFragment profiles, and sibling-star placement. -/
def checkAddressedDateFragmentFirstFilledComputation
    (model : FlatModel) (declaringGroup : GroupPath) (targetField : FieldId)
    (authored : SurfaceStarFieldPath) :
    Except AddressedDateFragmentFirstFilledComputationElabError
      (CheckedAddressedDateFragmentFirstFilledComputation model) := do
  let target ← checkAddressedFirstFilledTarget model declaringGroup targetField
    |>.mapError mapAddressedDateFragmentTargetError
  match hTarget : target.declaration.temporalFirstFilledStarCarrier? with
  | none => throw (.targetCarrier target.declaration.path)
  | some carrier =>
      if hFragment : carrier.isDateFragment then
        let source ← elaborateStarFieldPath model declaringGroup authored
          |>.mapError .source
        if hSource :
            source.declaration.temporalFirstFilledStarCarrier? = some carrier then
          let placement ← checkAddressedFirstFilledStarPlacement target source
            |>.mapError mapAddressedDateFragmentPlacementError
          pure {
            checkedTarget := target
            checkedSource := source
            placement
            carrier
            carrierIsFragment := hFragment
            targetCarrier := hTarget
            sourceCarrier := hSource
          }
        else
          throw (.sourceCarrier source.declaration.path carrier
            source.declaration.temporalFirstFilledStarCarrier?)
      else
        throw (.targetCarrier target.declaration.path)

inductive AddressedDateFragmentFirstFilledComputationFault where
  | targetRows (cause : ActualRowEnvironmentError)
  | targetEnvironment (cause : EnvBindingError)
  | source (cause : CheckedAddressingError)
  deriving Repr, DecidableEq

/-- DateFragment first-filled's public name for the shared exact-address token outcome. -/
abbrev AddressedDateFragmentFirstFilledComputationOutcome :=
  AddressedTokenComputationOutcome

/-- One checked addressed DateFragment result backed by the common exact-address String channels. -/
structure AddressedDateFragmentFirstFilledComputationRunView
    (model : FlatModel) (ResidualMessage : Type) where
  private mk ::
  operation : CheckedAddressedDateFragmentFirstFilledComputation model
  string : StringComputationRunView ResidualMessage CellAddr

namespace CheckedAddressedDateFragmentFirstFilledComputation

private def evaluateAtWithRead
    (operation : CheckedAddressedDateFragmentFirstFilledComputation model)
    (input : CheckedDocument model)
    (read : CellAddr → Except CheckedDocumentError CheckedCell)
    (environment : Env) :
    Except AddressedDateFragmentFirstFilledComputationFault
      AddressedDateFragmentFirstFilledComputationOutcome := do
  let targetPath ←
    environment.pathForScope operation.target.repeatableScope
      |>.mapError .targetEnvironment
  let resolved ← operation.source.resolveCheckedFieldWithRead input read environment
    |>.mapError .source
  pure {
    targetField := { field := operation.targetField, path := targetPath }
    result :=
      CheckedDateFragmentFirstFilledComputation.evalResolvedDateFragmentFirstFilled
        resolved
  }

/-- The no-value outcome an over-limit target row takes instead of a scan, retaining its exact
address so the application projection clears it. -/
def clearedAt (operation : CheckedAddressedDateFragmentFirstFilledComputation model)
    (environment : Env) :
    Except AddressedDateFragmentFirstFilledComputationFault
      AddressedDateFragmentFirstFilledComputationOutcome := do
  let targetPath ←
    environment.pathForScope operation.target.repeatableScope
      |>.mapError .targetEnvironment
  pure {
    targetField := { field := operation.targetField, path := targetPath }
    result := .noValue
  }

/-- Execute one sibling-correlated DateFragment scan per **in-capacity** target row through a caller-supplied exact-address source view, and only a clear at each over-limit row. Target topology, physical stored text, and immutable source target state remain unchanged. -/
def executeWithRead
    (operation : CheckedAddressedDateFragmentFirstFilledComputation model)
    (input : CheckedDocument model)
    (read : CellAddr → Except CheckedDocumentError CheckedCell) :
    Except AddressedDateFragmentFirstFilledComputationFault
      (List AddressedDateFragmentFirstFilledComputationOutcome) := do
  input.computationRowOutcomes operation.target.repeatableScope .targetRows
    operation.clearedAt (operation.evaluateAtWithRead input read)

/-- Execute one sibling-correlated DateFragment scan per in-capacity target row in document order, and a clear at each over-limit row. -/
def execute
    (operation : CheckedAddressedDateFragmentFirstFilledComputation model)
    (input : CheckedDocument model) :
    Except AddressedDateFragmentFirstFilledComputationFault
      (List AddressedDateFragmentFirstFilledComputationOutcome) :=
  operation.executeWithRead input input.read

/-- Classify caller-view token outcomes against immutable source target state through the shared String result owner. -/
def executeResultWithRead
    (operation : CheckedAddressedDateFragmentFirstFilledComputation model)
    (input : CheckedDocument model)
    (read : CellAddr → Except CheckedDocumentError CheckedCell)
    (residualMessages : List ResidualMessage) :
    Except AddressedDateFragmentFirstFilledComputationFault
      (AddressedDateFragmentFirstFilledComputationRunView model ResidualMessage) := do
  let outcomes ← operation.executeWithRead input read
  pure {
    operation
    string := projectAddressedTokenResults input residualMessages outcomes
  }

/-- Classify every exact token outcome against immutable source target state through the shared String result owner. -/
def executeResult
    (operation : CheckedAddressedDateFragmentFirstFilledComputation model)
    (input : CheckedDocument model) (residualMessages : List ResidualMessage) :
    Except AddressedDateFragmentFirstFilledComputationFault
      (AddressedDateFragmentFirstFilledComputationRunView model ResidualMessage) :=
  operation.executeResultWithRead input input.read residualMessages

end CheckedAddressedDateFragmentFirstFilledComputation

namespace AddressedDateFragmentFirstFilledComputationRunView

/-- Apply only retained exact-address DateFragment actions to a separate same-model destination projection. -/
def applyToChecked
    (view : AddressedDateFragmentFirstFilledComputationRunView
      model ResidualMessage)
    (destination : CheckedDocument model) :
    Except (StringComputationRunView.StringComputationRunApplicationError
      CellAddr) (StringComputationDestination CellAddr) :=
  view.string.applyTo destination.sourceStringTargetStateAt

end AddressedDateFragmentFirstFilledComputationRunView

end A12Kernel
