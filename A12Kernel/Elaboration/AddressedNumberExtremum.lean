import A12Kernel.Elaboration.AddressedNumberField

/-! # Same-scope repeatable direct-Number extrema

This capsule retains two ordered checked Number sources, delegates value selection to the existing scalar extrema semantics, and reuses the shared exact-address target owner.
-/

namespace A12Kernel

inductive AddressedNumberExtremumElabError where
  | pair (cause : AddressedNumberPairElabError)
  | scaleMismatch (target result : Nat)
  deriving Repr, DecidableEq

structure CheckedAddressedNumberExtremum (model : FlatModel) where
  private mk ::
  pair : CheckedAddressedNumberPair model
  op : NumericExtremumOp
  sameScale :
    pair.left.placement.targetPolicy.info.scale =
      max pair.left.source.info.scale pair.right.source.info.scale

def checkAddressedNumberExtremum
    (model : FlatModel) (declaringGroup : GroupPath) (targetField : FieldId)
    (leftReference rightReference : SurfaceFieldPath)
    (op : NumericExtremumOp) :
    Except AddressedNumberExtremumElabError
      (CheckedAddressedNumberExtremum model) := do
  let pair ←
    checkAddressedNumberPair model declaringGroup targetField
      leftReference rightReference |>.mapError .pair
  let resultScale := max pair.left.source.info.scale pair.right.source.info.scale
  if hScale : pair.left.placement.targetPolicy.info.scale = resultScale then
    pure { pair, op, sameScale := hScale }
  else
    throw (.scaleMismatch pair.left.placement.targetPolicy.info.scale resultScale)

abbrev AddressedNumberExtremumFault := AddressedNumericLeafFault

namespace CheckedAddressedNumberExtremum

def execute (operation : CheckedAddressedNumberExtremum model)
    (input : CheckedDocument model) :
    Except AddressedNumberExtremumFault
      (List (SourcedNumericTargetOutcome CellAddr)) :=
  operation.pair.executeWith input operation.op.selectComputationResult

def executeResult
    (operation : CheckedAddressedNumberExtremum model)
    (input : CheckedDocument model)
    (payloadAt : CellAddr → Payload)
    (supplied : List (ComputationFormalMessage Payload)) :
    Except AddressedNumberExtremumFault
      (NumericComputationRunView
        (ComputationFormalMessage Payload) CellAddr) := do
  operation.pair.executeResultWith input operation.op.selectComputationResult
    payloadAt supplied

end CheckedAddressedNumberExtremum

end A12Kernel
