import A12Kernel.Elaboration.AddressedFirstFilledStar
import A12Kernel.Elaboration.AddressedNumericLeaf
import A12Kernel.Elaboration.FirstFilledValue

/-! # Exact-address repeatable Number `FirstFilledValue`

This capsule binds one repeatable Number target to one unfiltered, single-axis starred Number source with a nonempty outer binding prefix. Each physical target row supplies that prefix, so the source scan stays sibling-local. Number's exhausted scan produces the real value zero before the existing target checker runs; reached formal invalidity remains poison.
-/

namespace A12Kernel

inductive AddressedNumberFirstFilledComputationElabError where
  | target (cause : AddressedNumericPlacementElabError)
  | source (cause : StarNumberElabError)
  | placement (cause : AddressedFirstFilledStarPlacementElabError)
  | scaleMismatch (target source : Nat)
  deriving Repr, DecidableEq

/-- One checked Number sibling star composed with the shared exact-address Number target and the ordinary unsuppressed computation-assignment scale gate. -/
structure CheckedAddressedNumberFirstFilledComputation (model : FlatModel) where
  private mk ::
  target : CheckedAddressedNumericTarget model
  source : CheckedStarNumberSource model
  placement : CheckedFirstFilledStarPlacement model target.targetField
    target.targetDeclaration source.source
  targetAdmitted : exactNumericScaleComparisonAllowedWithSuppression false
    (NumericScaleSummary.field target.targetPolicy.info.scale)
    (NumericScaleSummary.field source.field.info.scale) = true

namespace CheckedAddressedNumberFirstFilledComputation

def declaringGroup
    (operation : CheckedAddressedNumberFirstFilledComputation model) : GroupPath :=
  operation.target.declaringGroup

def targetField
    (operation : CheckedAddressedNumberFirstFilledComputation model) : FieldId :=
  operation.target.targetField

def targetDeclaration
    (operation : CheckedAddressedNumberFirstFilledComputation model) :
    FlatFieldDecl :=
  operation.target.targetDeclaration

theorem sourceSingleReopenedAxis
    (operation : CheckedAddressedNumberFirstFilledComputation model) :
    operation.source.source.reopenedScope.length = 1 :=
  operation.placement.sourceSingleReopenedAxis

theorem sourceBindingNonempty
    (operation : CheckedAddressedNumberFirstFilledComputation model) :
    operation.source.source.bindingScope ≠ [] :=
  operation.placement.sourceBindingNonempty

theorem sourceBindingBound
    (operation : CheckedAddressedNumberFirstFilledComputation model) :
    operation.source.source.bindingScope.all
      operation.targetDeclaration.repeatableScope.contains = true :=
  operation.placement.sourceBindingBound

theorem targetNotReferenced
    (operation : CheckedAddressedNumberFirstFilledComputation model) :
    operation.source.source.declaration.id ≠ operation.targetField :=
  operation.placement.targetNotReferenced

end CheckedAddressedNumberFirstFilledComputation

/-- Check the Number target, source kind and star path, shared sibling placement, and exact field scale in that order. -/
def checkAddressedNumberFirstFilledComputation
    (model : FlatModel) (declaringGroup : GroupPath) (targetField : FieldId)
    (authored : SurfaceStarFieldPath) :
    Except AddressedNumberFirstFilledComputationElabError
      (CheckedAddressedNumberFirstFilledComputation model) := do
  let target ← checkAddressedNumericTarget model declaringGroup targetField
    |>.mapError .target
  let source ← elaborateStarNumberSource model declaringGroup authored
    |>.mapError .source
  let placement ← checkFirstFilledStarPlacement target.targetField
      target.targetDeclaration target.targetOwned target.targetRepeatable
      source.source
    |>.mapError .placement
  if hScale : exactNumericScaleComparisonAllowedWithSuppression false
      (NumericScaleSummary.field target.targetPolicy.info.scale)
      (NumericScaleSummary.field source.field.info.scale) = true then
    pure { target, source, placement, targetAdmitted := hScale }
  else
    throw (.scaleMismatch target.targetPolicy.info.scale source.field.info.scale)

abbrev AddressedNumberFirstFilledComputationFault := AddressedNumericLeafFault

/-- One checked addressed Number result retains the definition beside the shared exact numeric result channels. -/
structure AddressedNumberFirstFilledComputationRunView (model : FlatModel)
    (Payload : Type) where
  private mk ::
  operation : CheckedAddressedNumberFirstFilledComputation model
  numeric : NumericComputationRunView
    (ComputationFormalMessage Payload) CellAddr

namespace CheckedAddressedNumberFirstFilledComputation

private def evaluateAtEnvironment
    (operation : CheckedAddressedNumberFirstFilledComputation model)
    (input : CheckedDocument model) (environment : Env) :
    Except AddressedNumberFirstFilledComputationFault NumericComputationResult := do
  let resolved ← operation.source.source.resolveCheckedField input environment
    |>.mapError .sourceAddressing
  let side : ResolvedValueListSide .number := {
    cells := resolved.cells.map fun addressed =>
      operation.source.checkedValueListCell .computation addressed.cell
        addressed.environment
    hasUninstantiatedTail := resolved.topology.domain.hasOpenTail
    hasHaving := false
  }
  pure (evalFirstFilledNumber side).asComputationResult

/-- Execute one parent-local first-filled scan per physical target row through the shared Number target checker. Exact source target state is retained before any result projection. -/
def execute
    (operation : CheckedAddressedNumberFirstFilledComputation model)
    (input : CheckedDocument model) :
    Except AddressedNumberFirstFilledComputationFault
      (List (SourcedNumericTargetOutcome CellAddr)) :=
  operation.target.executeAtEnvironment input
    (operation.evaluateAtEnvironment input)

/-- Classify exact addressed outcomes against immutable source target state while retaining the checked operation for Analyze and Transform consumers. -/
def executeResult
    (operation : CheckedAddressedNumberFirstFilledComputation model)
    (input : CheckedDocument model) (payloadAt : CellAddr → Payload)
    (supplied : List (ComputationFormalMessage Payload)) :
    Except AddressedNumberFirstFilledComputationFault
      (AddressedNumberFirstFilledComputationRunView model Payload) := do
  let outcomes ← operation.execute input
  pure {
    operation
    numeric := NumericComputationRunView.fromSourceOutcomesWithMessages
      MessagePointer.ofCellAddr payloadAt supplied outcomes
  }

end CheckedAddressedNumberFirstFilledComputation

namespace AddressedNumberFirstFilledComputationRunView

/-- Apply only retained exact-address Number actions to a separately supplied same-model destination projection. -/
def applyToChecked
    (view : AddressedNumberFirstFilledComputationRunView model Payload)
    (destination : CheckedDocument model) :
    Except NumericComputationDocumentApplicationError
      (NumericComputationApplicationProjection model) :=
  view.numeric.applyToChecked destination

end AddressedNumberFirstFilledComputationRunView

end A12Kernel
