import A12Kernel.Elaboration.FullDateFirstFilledComputation
import A12Kernel.Elaboration.AddressedFirstFilledStar

/-! # Exact-address repeatable full-Date `FirstFilledValue`

This capsule binds one repeatable FULL Date target to a sibling one-axis starred FULL Date source with the same exact format. Every target row supplies the shared outer prefix, selection stays parent-local in the exact-instant domain, and the target policy retains accepted values, rejected attempts, clean absence, and formal poison under exact cell addresses. Application remains a target-state projection and does not reconstruct a document or run validation.
-/

namespace A12Kernel

inductive AddressedFullDateFirstFilledComputationElabError where
  | target (cause : ResolveError)
  | targetOutsideDeclaringGroup (path declaringGroup : GroupPath)
  | targetNotRepeatable (path : List String)
  | targetPolicy (cause : FullDateTargetElabError)
  | source (cause : StarPathElabError)
  | sourceCarrier (path : List String)
  | sourceShape (path : List String)
  | sourceScope (path : List String)
  | targetSelfReference (field : FieldId)
  deriving Repr, DecidableEq

/-- One exact-format repeatable FULL Date target and sibling source tied to the same checked model. -/
structure CheckedAddressedFullDateFirstFilledShape
    (model : FlatModel) (carrier : TemporalFirstFilledStarCarrier) where
  private mk ::
  checkedTarget : CheckedAddressedFirstFilledTarget model
  checkedSource : CheckedStarFieldPath model
  sourceCarrier :
    checkedSource.declaration.temporalFirstFilledStarCarrier? = some carrier
  placement : CheckedAddressedFirstFilledStarPlacement model
    checkedTarget checkedSource

/-- The two admitted exact FULL Date spelling profiles. -/
inductive AddressedFullDateFirstFilledShape (model : FlatModel) where
  | iso
      (shape : CheckedAddressedFullDateFirstFilledShape model .fullDateIso)
  | dotted
      (shape : CheckedAddressedFullDateFirstFilledShape model .fullDateDotted)

/-- One addressed FULL Date computation with its checked target rendering and rejection policy. -/
structure CheckedAddressedFullDateFirstFilledComputation (model : FlatModel) where
  private mk ::
  shape : AddressedFullDateFirstFilledShape model
  targetPolicy : CheckedFullDateTarget model

namespace CheckedAddressedFullDateFirstFilledComputation

def target
    (operation : CheckedAddressedFullDateFirstFilledComputation model) :
    FlatFieldDecl :=
  match operation.shape with
  | .iso shape | .dotted shape => shape.checkedTarget.declaration

def targetField
    (operation : CheckedAddressedFullDateFirstFilledComputation model) :
    FieldId :=
  match operation.shape with
  | .iso shape | .dotted shape => shape.checkedTarget.targetField

def source
    (operation : CheckedAddressedFullDateFirstFilledComputation model) :
    CheckedStarFieldPath model :=
  match operation.shape with
  | .iso shape | .dotted shape => shape.checkedSource

end CheckedAddressedFullDateFirstFilledComputation

private def mapAddressedFullDateTargetError :
    AddressedFirstFilledTargetElabError →
      AddressedFullDateFirstFilledComputationElabError
  | .target cause => .target cause
  | .targetOutsideDeclaringGroup path declaringGroup =>
      .targetOutsideDeclaringGroup path declaringGroup
  | .targetNotRepeatable path => .targetNotRepeatable path

private def mapAddressedFullDatePlacementError :
    AddressedFirstFilledStarPlacementElabError →
      AddressedFullDateFirstFilledComputationElabError
  | .sourceShape path => .sourceShape path
  | .sourceScope path => .sourceScope path
  | .targetSelfReference field => .targetSelfReference field

private def checkAddressedFullDateFirstFilledShape
    (model : FlatModel) (target : CheckedAddressedFirstFilledTarget model)
    (authored : SurfaceStarFieldPath)
    (carrier : TemporalFirstFilledStarCarrier) :
    Except AddressedFullDateFirstFilledComputationElabError
      (CheckedAddressedFullDateFirstFilledShape model carrier) := do
  let source ← elaborateStarFieldPath model target.declaringGroup authored
    |>.mapError .source
  if hSource : source.declaration.temporalFirstFilledStarCarrier? =
      some carrier then
    let placement ← checkAddressedFirstFilledStarPlacement target source
      |>.mapError mapAddressedFullDatePlacementError
    pure {
      checkedTarget := target
      checkedSource := source
      sourceCarrier := hSource
      placement
    }
  else
    throw (.sourceCarrier source.declaration.path)

/-- Check repeatable target placement, exact FULL Date carrier identity, target policy, and sibling-star placement. -/
def checkAddressedFullDateFirstFilledComputation
    (model : FlatModel) (declaringGroup : GroupPath) (targetField : FieldId)
    (authored : SurfaceStarFieldPath) :
    Except AddressedFullDateFirstFilledComputationElabError
      (CheckedAddressedFullDateFirstFilledComputation model) := do
  let target ← checkAddressedFirstFilledTarget model declaringGroup targetField
    |>.mapError mapAddressedFullDateTargetError
  let targetPolicy ← elaborateFullDateTargetIn model
      target.declaration.repeatableScope targetField
    |>.mapError .targetPolicy
  match targetPolicy.format with
  | .yearMonthDayDashes =>
      let shape ← checkAddressedFullDateFirstFilledShape model target authored
        .fullDateIso
      pure { shape := .iso shape, targetPolicy }
  | .dayMonthYearDots =>
      let shape ← checkAddressedFullDateFirstFilledShape model target authored
        .fullDateDotted
      pure { shape := .dotted shape, targetPolicy }

inductive AddressedFullDateFirstFilledComputationFault where
  | targetRows (cause : ActualRowEnvironmentError)
  | targetEnvironment (cause : EnvBindingError)
  | source (cause : CheckedAddressingError)
  | target (cause : FullDateTargetEvaluationFault)
  deriving Repr, DecidableEq

/-- One sibling-local FULL Date selection retained under its exact target address. -/
structure AddressedFullDateFirstFilledComputationOutcome where
  targetField : CellAddr
  outcome : FullDateTargetOutcome
  deriving Repr, DecidableEq

/-- One checked addressed FULL Date result backed by the common five FullDate channels over exact cell addresses. -/
structure AddressedFullDateFirstFilledComputationRunView (model : FlatModel)
    (ResidualMessage : Type) where
  private mk ::
  operation : CheckedAddressedFullDateFirstFilledComputation model
  fullDate : FullDateComputationRunView ResidualMessage CellAddr

namespace CheckedAddressedFullDateFirstFilledComputation

private def evaluateAtWithRead
    (operation : CheckedAddressedFullDateFirstFilledComputation model)
    (input : CheckedDocument model)
    (read : CellAddr → Except CheckedDocumentError CheckedCell)
    (environment : Env) :
    Except AddressedFullDateFirstFilledComputationFault
      AddressedFullDateFirstFilledComputationOutcome := do
  let targetPath ←
    environment.pathForScope operation.target.repeatableScope
      |>.mapError .targetEnvironment
  let resolved ← operation.source.resolveCheckedFieldWithRead input read environment
    |>.mapError .source
  let outcome ← operation.targetPolicy.evaluate
      (evalFullDateFirstFilledCells resolved.cells)
    |>.mapError .target
  pure {
    targetField := { field := operation.targetField, path := targetPath }
    outcome
  }

/-- Execute one sibling-correlated FULL Date scan per physical target row through a caller-supplied exact-address source view. Target topology, physical stored text, and immutable source target state remain unchanged. -/
def executeWithRead
    (operation : CheckedAddressedFullDateFirstFilledComputation model)
    (input : CheckedDocument model)
    (read : CellAddr → Except CheckedDocumentError CheckedCell) :
    Except AddressedFullDateFirstFilledComputationFault
      (List AddressedFullDateFirstFilledComputationOutcome) := do
  let environments ← input.actualRowEnvironments operation.target.repeatableScope
    |>.mapError .targetRows
  environments.mapM (operation.evaluateAtWithRead input read)

/-- Execute one sibling-correlated FULL Date scan per physical target row in document order. -/
def execute
    (operation : CheckedAddressedFullDateFirstFilledComputation model)
    (input : CheckedDocument model) :
    Except AddressedFullDateFirstFilledComputationFault
      (List AddressedFullDateFirstFilledComputationOutcome) :=
  operation.executeWithRead input input.read

/-- Classify caller-view outcomes against immutable source target state through the shared FullDate result owner. -/
def executeResultWithRead
    (operation : CheckedAddressedFullDateFirstFilledComputation model)
    (input : CheckedDocument model)
    (read : CellAddr → Except CheckedDocumentError CheckedCell)
    (residualMessages : List ResidualMessage) :
    Except AddressedFullDateFirstFilledComputationFault
      (AddressedFullDateFirstFilledComputationRunView model ResidualMessage) := do
  let outcomes ← operation.executeWithRead input read
  pure {
    operation
    fullDate := FullDateComputationRunView.fromOutcomesAt
      input.sourceFullDateTargetStateAt residualMessages
      (outcomes.map fun entry => (entry.targetField, entry.outcome))
  }

/-- Classify every exact row outcome against immutable source target state through the shared FullDate result owner. -/
def executeResult
    (operation : CheckedAddressedFullDateFirstFilledComputation model)
    (input : CheckedDocument model) (residualMessages : List ResidualMessage) :
    Except AddressedFullDateFirstFilledComputationFault
      (AddressedFullDateFirstFilledComputationRunView model ResidualMessage) :=
  operation.executeResultWithRead input input.read residualMessages

end CheckedAddressedFullDateFirstFilledComputation

namespace AddressedFullDateFirstFilledComputationRunView

/-- Apply retained source-relative actions to exact FullDate cell-state projections from a separate checked document of the same model. -/
def applyToChecked
    (view : AddressedFullDateFirstFilledComputationRunView model ResidualMessage)
    (destination : CheckedDocument model) :
    Except (FullDateComputationRunView.FullDateComputationRunApplicationError
      CellAddr) (FullDateComputationDestination CellAddr) :=
  view.fullDate.applyTo destination.sourceFullDateTargetStateAt

end AddressedFullDateFirstFilledComputationRunView

end A12Kernel
