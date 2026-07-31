import A12Kernel.Elaboration.AddressedNumberField

/-! # Same-scope repeatable direct-Number extrema

This capsule retains two ordered checked Number sources, delegates value selection to the existing scalar extrema semantics, and reuses the shared exact-address target owner.
-/

namespace A12Kernel

inductive AddressedNumberExtremumElabError where
  | left (cause : AddressedNumberSourceElabError)
  | right (cause : AddressedNumberSourceElabError)
  | incoherentTarget (left right : FieldId)
  | scaleMismatch (target result : Nat)
  deriving Repr, DecidableEq

structure CheckedAddressedNumberExtremum (model : FlatModel) where
  private mk ::
  left : CheckedAddressedNumberSource model
  right : CheckedAddressedNumberSource model
  op : NumericExtremumOp
  sameTarget : left.placement.targetField = right.placement.targetField
  sameScale :
    left.placement.targetPolicy.info.scale =
      max left.source.info.scale right.source.info.scale

def checkAddressedNumberExtremum
    (model : FlatModel) (declaringGroup : GroupPath) (targetField : FieldId)
    (leftReference rightReference : SurfaceFieldPath)
    (op : NumericExtremumOp) :
    Except AddressedNumberExtremumElabError
      (CheckedAddressedNumberExtremum model) := do
  let left ←
    checkAddressedNumberSource model declaringGroup targetField leftReference
      |>.mapError .left
  let right ←
    checkAddressedNumberSource model declaringGroup targetField rightReference
      |>.mapError .right
  if hTarget : left.placement.targetField = right.placement.targetField then
    let resultScale := max left.source.info.scale right.source.info.scale
    if hScale : left.placement.targetPolicy.info.scale = resultScale then
      pure { left, right, op, sameTarget := hTarget, sameScale := hScale }
    else
      throw (.scaleMismatch left.placement.targetPolicy.info.scale resultScale)
  else
    throw (.incoherentTarget left.placement.targetField
      right.placement.targetField)

abbrev AddressedNumberExtremumFault := AddressedNumericLeafFault

namespace CheckedAddressedNumberExtremum

private def evaluateSourceAtPath
    (source : CheckedAddressedNumberSource model)
    (input : CheckedDocument model) (path : List Nat) :
    Except AddressedNumberExtremumFault NumericComputationResult := do
  let address : CellAddr := {
    field := source.placement.sourceDeclaration.id
    path
  }
  let cell ← (input.read address).mapError .sourceRead
  (source.placement.evaluateSourceAtom cell
    (.field source.placement.sourceDeclaration)).mapError .evaluation

private def evaluateAtPath
    (operation : CheckedAddressedNumberExtremum model)
    (input : CheckedDocument model) (path : List Nat) :
    Except AddressedNumberExtremumFault NumericComputationResult := do
  let leftResult ← evaluateSourceAtPath operation.left input path
  match leftResult with
  | .poison cause => pure (.poison cause)
  | .value _ | .domainFailure =>
      let rightResult ← evaluateSourceAtPath operation.right input path
      pure (operation.op.selectComputationResult leftResult rightResult)

def execute (operation : CheckedAddressedNumberExtremum model)
    (input : CheckedDocument model) :
    Except AddressedNumberExtremumFault
      (List (SourcedNumericTargetOutcome CellAddr)) :=
  operation.left.placement.executeWithPath input
    (operation.evaluateAtPath input)

def executeResult
    (operation : CheckedAddressedNumberExtremum model)
    (input : CheckedDocument model)
    (payloadAt : CellAddr → Payload)
    (supplied : List (ComputationFormalMessage Payload)) :
    Except AddressedNumberExtremumFault
      (NumericComputationRunView
        (ComputationFormalMessage Payload) CellAddr) := do
  let outcomes ← operation.execute input
  pure (NumericComputationRunView.fromSourceOutcomesWithMessages
    ComputationErrorPointer.ofCellAddr payloadAt supplied outcomes)

end CheckedAddressedNumberExtremum

end A12Kernel
