import A12Kernel.Elaboration.CustomFirstFilledComputation
import A12Kernel.Elaboration.AddressedFirstFilledStar

/-! # Exact-address repeatable Custom `FirstFilledValue`

This capsule binds one repeatable Custom target to a one-axis starred source carrying the same Custom type declaration and a nonempty outer binding prefix. Every physical target row supplies that prefix, so sibling scans stay parent-local. Runtime selection consumes the prepared checked cells without resampling the validator, then reuses the exact-address String result and application channels.
-/

namespace A12Kernel

inductive AddressedCustomFirstFilledComputationElabError where
  | target (cause : ResolveError)
  | targetOutsideDeclaringGroup (path declaringGroup : GroupPath)
  | targetNotRepeatable (path : List String)
  | targetNotCustom (path : List String)
  | source (cause : StarPathElabError)
  | sourceCustomTypeMismatch (path : List String)
      (expected : CustomFieldTypeDeclaration)
      (actual : Option CustomFieldTypeDeclaration)
  | sourceShape (path : List String)
  | sourceScope (path : List String)
  | targetSelfReference (field : FieldId)
  deriving Repr, DecidableEq

/-- One repeatable Custom target and one checked single-reopened-axis source carrying the same Custom declaration. -/
structure CheckedAddressedCustomFirstFilledComputation (model : FlatModel) where
  private mk ::
  checkedTarget : CheckedAddressedFirstFilledTarget model
  checkedSource : CheckedStarFieldPath model
  placement : CheckedAddressedFirstFilledStarPlacement model
    checkedTarget checkedSource
  customType : CustomFieldTypeDeclaration
  targetCustom : checkedTarget.declaration.customType = some customType
  sourceCustom : checkedSource.declaration.customType = some customType

namespace CheckedAddressedCustomFirstFilledComputation

def declaringGroup
    (operation : CheckedAddressedCustomFirstFilledComputation model) : GroupPath :=
  operation.checkedTarget.declaringGroup

def targetField
    (operation : CheckedAddressedCustomFirstFilledComputation model) : FieldId :=
  operation.checkedTarget.targetField

def target
    (operation : CheckedAddressedCustomFirstFilledComputation model) : FlatFieldDecl :=
  operation.checkedTarget.declaration

def source
    (operation : CheckedAddressedCustomFirstFilledComputation model) :
    CheckedStarFieldPath model :=
  operation.checkedSource

theorem targetOwned
    (operation : CheckedAddressedCustomFirstFilledComputation model) :
    model.lookupUniqueId operation.targetField = .ok operation.target :=
  operation.checkedTarget.owned

theorem targetInDeclaringGroup
    (operation : CheckedAddressedCustomFirstFilledComputation model) :
    operation.target.groupPath = operation.declaringGroup :=
  operation.checkedTarget.inDeclaringGroup

theorem targetRepeatable
    (operation : CheckedAddressedCustomFirstFilledComputation model) :
    operation.target.repeatableScope ≠ [] :=
  operation.checkedTarget.repeatable

theorem sourceSingleReopenedAxis
    (operation : CheckedAddressedCustomFirstFilledComputation model) :
    operation.source.reopenedScope.length = 1 :=
  operation.placement.sourceSingleReopenedAxis

theorem sourceBindingBound
    (operation : CheckedAddressedCustomFirstFilledComputation model) :
    operation.source.bindingScope.all operation.target.repeatableScope.contains = true :=
  operation.placement.sourceBindingBound

theorem sourceBindingNonempty
    (operation : CheckedAddressedCustomFirstFilledComputation model) :
    operation.source.bindingScope ≠ [] :=
  operation.placement.sourceBindingNonempty

theorem targetNotReferenced
    (operation : CheckedAddressedCustomFirstFilledComputation model) :
    operation.source.declaration.id ≠ operation.targetField :=
  operation.placement.targetNotReferenced

end CheckedAddressedCustomFirstFilledComputation

private def mapAddressedCustomTargetError :
    AddressedFirstFilledTargetElabError →
      AddressedCustomFirstFilledComputationElabError
  | .target cause => .target cause
  | .targetOutsideDeclaringGroup path declaringGroup =>
      .targetOutsideDeclaringGroup path declaringGroup
  | .targetNotRepeatable path => .targetNotRepeatable path

private def mapAddressedCustomStarPlacementError :
    AddressedFirstFilledStarPlacementElabError →
      AddressedCustomFirstFilledComputationElabError
  | .sourceShape path => .sourceShape path
  | .sourceScope path => .sourceScope path
  | .targetSelfReference field => .targetSelfReference field

/-- Check the target first, then retain Custom declaration identity and the source-star binding certificate. -/
def checkAddressedCustomFirstFilledComputation
    (model : FlatModel) (declaringGroup : GroupPath) (targetField : FieldId)
    (authored : SurfaceStarFieldPath) :
    Except AddressedCustomFirstFilledComputationElabError
      (CheckedAddressedCustomFirstFilledComputation model) :=
  do
    let target ← checkAddressedFirstFilledTarget model declaringGroup targetField
      |>.mapError mapAddressedCustomTargetError
    match hCustom : target.declaration.customType with
    | none => throw (.targetNotCustom target.declaration.path)
    | some customType =>
      let source ← elaborateStarFieldPath model declaringGroup authored
        |>.mapError .source
      if hSource : source.declaration.customType = some customType then
        let placement ← checkAddressedFirstFilledStarPlacement target source
          |>.mapError mapAddressedCustomStarPlacementError
        pure {
          checkedTarget := target
          checkedSource := source
          placement
          customType
          targetCustom := hCustom
          sourceCustom := hSource
        }
      else
        throw (.sourceCustomTypeMismatch source.declaration.path customType
          source.declaration.customType)

inductive AddressedCustomFirstFilledComputationFault where
  | targetRows (cause : ActualRowEnvironmentError)
  | targetEnvironment (cause : EnvBindingError)
  | source (cause : CheckedAddressingError)
  deriving Repr, DecidableEq

/-- Custom first-filled's public name for the shared exact-address token outcome. -/
abbrev AddressedCustomFirstFilledComputationOutcome :=
  AddressedTokenComputationOutcome

/-- One checked addressed Custom result backed by the common exact-address String channels. -/
structure AddressedCustomFirstFilledComputationRunView (model : FlatModel)
    (ResidualMessage : Type) where
  private mk ::
  operation : CheckedAddressedCustomFirstFilledComputation model
  string : StringComputationRunView ResidualMessage CellAddr

namespace CheckedAddressedCustomFirstFilledComputation

private def evaluateAtWithRead
    (operation : CheckedAddressedCustomFirstFilledComputation model)
    (input : CheckedDocument model)
    (read : CellAddr → Except CheckedDocumentError CheckedCell)
    (environment : Env) :
    Except AddressedCustomFirstFilledComputationFault
      AddressedCustomFirstFilledComputationOutcome := do
  let targetPath ←
    environment.pathForScope operation.target.repeatableScope
      |>.mapError .targetEnvironment
  let resolved ← operation.source.resolveCheckedFieldWithRead input read environment
    |>.mapError .source
  let side : ResolvedValueListSide .token := {
    cells := resolved.cells.map fun cell => customFirstFilledCellAt cell.cell
    hasUninstantiatedTail := resolved.topology.domain.hasOpenTail
    hasHaving := false
  }
  pure {
    targetField := { field := operation.targetField, path := targetPath }
    result := (evalFirstFilledToken side).asComputationResult
  }

/-- Execute one sibling-correlated Custom scan per physical target row through a caller-supplied exact-address source view. Target topology, prepared Custom validation, and immutable source target state remain unchanged. -/
def executeWithRead
    (operation : CheckedAddressedCustomFirstFilledComputation model)
    (input : CheckedDocument model)
    (read : CellAddr → Except CheckedDocumentError CheckedCell) :
    Except AddressedCustomFirstFilledComputationFault
      (List AddressedCustomFirstFilledComputationOutcome) := do
  let environments ← input.actualRowEnvironments operation.target.repeatableScope
    |>.mapError .targetRows
  environments.mapM (operation.evaluateAtWithRead input read)

/-- Execute one prepared, sibling-correlated Custom scan per physical target row in document order. -/
def execute
    (operation : CheckedAddressedCustomFirstFilledComputation model)
    (input : CheckedDocument model) :
    Except AddressedCustomFirstFilledComputationFault
      (List AddressedCustomFirstFilledComputationOutcome) :=
  operation.executeWithRead input input.read

/-- Classify caller-view outcomes against immutable source target state through the shared String result owner. -/
def executeResultWithRead
    (operation : CheckedAddressedCustomFirstFilledComputation model)
    (input : CheckedDocument model)
    (read : CellAddr → Except CheckedDocumentError CheckedCell)
    (residualMessages : List ResidualMessage) :
    Except AddressedCustomFirstFilledComputationFault
      (AddressedCustomFirstFilledComputationRunView model ResidualMessage) := do
  let outcomes ← operation.executeWithRead input read
  pure {
    operation
    string := projectAddressedTokenResults input residualMessages outcomes
  }

/-- Classify every immutable exact token outcome against source target state through the shared String result owner. -/
def executeResult
    (operation : CheckedAddressedCustomFirstFilledComputation model)
    (input : CheckedDocument model) (residualMessages : List ResidualMessage) :
    Except AddressedCustomFirstFilledComputationFault
      (AddressedCustomFirstFilledComputationRunView model ResidualMessage) :=
  operation.executeResultWithRead input input.read residualMessages

end CheckedAddressedCustomFirstFilledComputation

namespace AddressedCustomFirstFilledComputationRunView

/-- Apply only retained exact-address Custom actions to a separate same-model destination projection without resampling validation. -/
def applyToChecked
    (view : AddressedCustomFirstFilledComputationRunView model ResidualMessage)
    (destination : CheckedDocument model) :
    Except (StringComputationRunView.StringComputationRunApplicationError CellAddr)
      (StringComputationDestination CellAddr) :=
  view.string.applyTo destination.sourceStringTargetStateAt

end AddressedCustomFirstFilledComputationRunView

end A12Kernel
