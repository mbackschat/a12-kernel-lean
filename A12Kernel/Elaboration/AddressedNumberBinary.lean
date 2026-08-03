import A12Kernel.Elaboration.AddressedNumberField

/-! # Same-scope repeatable direct-Number binary arithmetic

This capsule retains two ordered checked Number sources, delegates each arithmetic node to the existing precision-50 semantics, and reuses the shared exact-address target owner.
-/

namespace A12Kernel

inductive AddressedNumberBinaryElabError where
  | pair (cause : AddressedNumberPairElabError)
  | scaleMismatch (target result : Nat)
  deriving Repr, DecidableEq

structure CheckedAddressedNumberBinary (model : FlatModel) where
  private mk ::
  pair : CheckedAddressedNumberPair model
  op : NumericArithmeticOp
  sameScale :
    pair.left.placement.targetPolicy.info.scale =
      op.directFieldResultScale pair.left.source.info.scale
        pair.right.source.info.scale

def checkAddressedNumberBinary
    (model : FlatModel) (declaringGroup : GroupPath) (targetField : FieldId)
    (leftReference rightReference : SurfaceFieldPath)
    (op : NumericArithmeticOp) :
    Except AddressedNumberBinaryElabError
      (CheckedAddressedNumberBinary model) := do
  let pair ←
    checkAddressedNumberPair model declaringGroup targetField
      leftReference rightReference |>.mapError .pair
  let resultScale := op.directFieldResultScale
    pair.left.source.info.scale pair.right.source.info.scale
  if hScale : pair.left.placement.targetPolicy.info.scale = resultScale then
    pure { pair, op, sameScale := hScale }
  else
    throw (.scaleMismatch pair.left.placement.targetPolicy.info.scale resultScale)

abbrev AddressedNumberBinaryFault := AddressedNumericLeafFault

namespace CheckedAddressedNumberBinary

private def combine (operation : CheckedAddressedNumberBinary model)
    (left right : NumericComputationResult) : NumericComputationResult :=
  NumericComputationResult.combineReached
    (fun leftValue rightValue => .value (operation.op.eval leftValue rightValue))
    left right

def execute (operation : CheckedAddressedNumberBinary model)
    (input : CheckedDocument model) :
    Except AddressedNumberBinaryFault
      (List (SourcedNumericTargetOutcome CellAddr)) :=
  operation.pair.executeWith input operation.combine

def executeResult
    (operation : CheckedAddressedNumberBinary model)
    (input : CheckedDocument model)
    (payloadAt : CellAddr → Payload)
    (supplied : List (ComputationFormalMessage Payload)) :
    Except AddressedNumberBinaryFault
      (NumericComputationRunView
        (ComputationFormalMessage Payload) CellAddr) :=
  operation.pair.executeResultWith input operation.combine payloadAt supplied

end CheckedAddressedNumberBinary

end A12Kernel
