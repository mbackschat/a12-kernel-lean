import A12Kernel.Elaboration.AddressedFirstFilledStar
import A12Kernel.Elaboration.AddressedNumericLeaf
import A12Kernel.Elaboration.FirstFilledValue

/-! # Exact-address repeatable Number `FirstFilledValue`

This capsule binds one repeatable Number target to a nonempty authored list of unfiltered, single-axis starred Number sources with nonempty outer binding prefixes. Each physical target row supplies every prefix, so each source extent stays sibling-local. The shared entity-list evaluator exhausts sources in authored order, preserves empty-prefix polarity, and stops before every later semantic or structural read after a value or poison. Number's exhausted scan produces the real value zero before the existing target checker runs.
-/

namespace A12Kernel

inductive AddressedNumberFirstFilledOperandElabError where
  | source (cause : StarNumberElabError)
  | placement (cause : AddressedFirstFilledStarPlacementElabError)
  | scaleMismatch (target source : Nat)
  deriving Repr, DecidableEq

inductive AddressedNumberFirstFilledComputationElabError where
  | target (cause : AddressedNumericPlacementElabError)
  | operand (index : Nat) (cause : AddressedNumberFirstFilledOperandElabError)
  deriving Repr, DecidableEq

/-- One checked Number sibling-star operand composed with one already checked exact-address target. -/
structure CheckedAddressedNumberFirstFilledOperand (model : FlatModel)
    (target : CheckedAddressedNumericTarget model) where
  private mk ::
  source : CheckedStarNumberSource model
  placement : CheckedFirstFilledStarPlacement model target.targetField
    target.targetDeclaration source.source
  targetAdmitted : exactNumericScaleComparisonAllowedWithSuppression false
    (NumericScaleSummary.field target.targetPolicy.info.scale)
    (NumericScaleSummary.field source.field.info.scale) = true

/-- One checked nonempty authored list of Number sibling stars sharing the exact target by construction. -/
structure CheckedAddressedNumberFirstFilledComputation (model : FlatModel) where
  private mk ::
  target : CheckedAddressedNumericTarget model
  first : CheckedAddressedNumberFirstFilledOperand model target
  rest : List (CheckedAddressedNumberFirstFilledOperand model target)

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

def operands (operation : CheckedAddressedNumberFirstFilledComputation model) :
    List (CheckedAddressedNumberFirstFilledOperand model operation.target) :=
  operation.first :: operation.rest

def sources (operation : CheckedAddressedNumberFirstFilledComputation model) :
    List (CheckedStarNumberSource model) :=
  operation.operands.map (·.source)

def sourceFields
    (operation : CheckedAddressedNumberFirstFilledComputation model) :
    List FieldId :=
  operation.sources.map (·.source.declaration.id)

/-- Compatibility view of the first operand for callers whose behavior is genuinely first-source-specific. -/
def source (operation : CheckedAddressedNumberFirstFilledComputation model) :
    CheckedStarNumberSource model :=
  operation.first.source

/-- Compatibility view of the first operand's placement certificate. -/
def placement
    (operation : CheckedAddressedNumberFirstFilledComputation model) :
    CheckedFirstFilledStarPlacement model operation.targetField
      operation.targetDeclaration operation.source.source :=
  operation.first.placement

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

private theorem starredOperandsHaveNoDirectDuplicate
    {target : CheckedAddressedNumericTarget model}
    (operands : List (CheckedAddressedNumberFirstFilledOperand model target)) :
    firstDuplicateDirectNumberEntityField?
      (operands.map fun operand => .star operand.source) = none := by
  induction operands with
  | nil => rfl
  | cons operand remaining ih =>
      change firstDuplicateOptionalIdentity?
        (fun candidate : CheckedNumberEntityOperand model =>
          candidate.directFieldId?)
        (.star operand.source :: remaining.map fun candidate =>
          .star candidate.source) = none
      rw [firstDuplicateOptionalIdentity?]
      exact ih

/-- Reuse the complete checked Number entity-list evaluator without reopening direct, group, or filtered authoring at this bounded addressed surface. -/
def numberSource
    (operation : CheckedAddressedNumberFirstFilledComputation model) :
    CheckedFirstFilledNumberSource model := {
  first := .star operation.first.source
  rest := operation.rest.map fun operand => .star operand.source
  modelWellFormed := operation.target.modelWellFormed
  requiredMultiplicity := rfl
  uniqueDirectOperands := by
    simpa [operands] using
      starredOperandsHaveNoDirectDuplicate operation.operands
}

end CheckedAddressedNumberFirstFilledComputation

private def checkAddressedNumberFirstFilledOperand
    (model : FlatModel) (declaringGroup : GroupPath)
    (target : CheckedAddressedNumericTarget model) (index : Nat)
    (authored : SurfaceStarFieldPath) :
    Except AddressedNumberFirstFilledComputationElabError
      (CheckedAddressedNumberFirstFilledOperand model target) := do
  let source ← elaborateStarNumberSource model declaringGroup authored
    |>.mapError fun cause => .operand index (.source cause)
  let placement ← checkFirstFilledStarPlacement target.targetField
      target.targetDeclaration target.targetOwned target.targetRepeatable
      source.source
    |>.mapError fun cause => .operand index (.placement cause)
  if hScale : exactNumericScaleComparisonAllowedWithSuppression false
      (NumericScaleSummary.field target.targetPolicy.info.scale)
      (NumericScaleSummary.field source.field.info.scale) = true then
    pure { source, placement, targetAdmitted := hScale }
  else
    throw (.operand index
      (.scaleMismatch target.targetPolicy.info.scale source.field.info.scale))

private def checkAddressedNumberFirstFilledRest
    (model : FlatModel) (declaringGroup : GroupPath)
    (target : CheckedAddressedNumericTarget model) :
    Nat → List SurfaceStarFieldPath →
      Except AddressedNumberFirstFilledComputationElabError
        (List (CheckedAddressedNumberFirstFilledOperand model target))
  | _, [] => pure []
  | index, authored :: remaining => do
      let first ← checkAddressedNumberFirstFilledOperand model declaringGroup
        target index authored
      let rest ← checkAddressedNumberFirstFilledRest model declaringGroup target
        (index + 1) remaining
      pure (first :: rest)

/-- Check the Number target, then each source's kind, sibling placement, and exact field scale in authored order. -/
def checkAddressedNumberFirstFilledComputation
    (model : FlatModel) (declaringGroup : GroupPath) (targetField : FieldId)
    (authored : SurfaceStarFieldPath)
    (remaining : List SurfaceStarFieldPath := []) :
    Except AddressedNumberFirstFilledComputationElabError
      (CheckedAddressedNumberFirstFilledComputation model) := do
  let target ← checkAddressedNumericTarget model declaringGroup targetField
    |>.mapError .target
  let first ← checkAddressedNumberFirstFilledOperand model declaringGroup target
    0 authored
  let rest ← checkAddressedNumberFirstFilledRest model declaringGroup target
    1 remaining
  pure { target, first, rest }

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
  let result ← operation.numberSource.evaluateCheckedDocumentComputation
      input environment
    |>.mapError .sourceAddressing
  pure result.asComputationResult

/-- Execute one authored-order parent-local first-filled scan per physical target row through the shared Number target checker. Exact source target state is retained before any result projection. -/
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
