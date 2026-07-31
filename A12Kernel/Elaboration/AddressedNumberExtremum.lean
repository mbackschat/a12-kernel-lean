import A12Kernel.Elaboration.AddressedNumberField

/-! # Same-scope repeatable direct-Number extrema

This capsule retains two or more ordered checked Number sources, delegates the authored-order fold to the existing scalar extrema semantics, and reuses the shared exact-address target owner.
-/

namespace A12Kernel

inductive AddressedNumberExtremumElabError where
  | pair (cause : AddressedNumberPairElabError)
  | additional (position : Nat) (cause : AddressedNumberSourceElabError)
  | incoherentAdditionalTarget
  | scaleMismatch (target result : Nat)
  deriving Repr, DecidableEq

private def checkAdditionalNumberSources
    (model : FlatModel) (declaringGroup : GroupPath) (targetField : FieldId) :
    Nat → List SurfaceFieldPath →
      Except AddressedNumberExtremumElabError
        (List (CheckedAddressedNumberSource model))
  | _, [] => pure []
  | position, reference :: rest => do
      let source ←
        checkAddressedNumberSource model declaringGroup targetField reference
          |>.mapError (.additional position)
      let tail ← checkAdditionalNumberSources model declaringGroup targetField
        (position + 1) rest
      pure (source :: tail)

def addressedNumberExtremumResultScale
    (pair : CheckedAddressedNumberPair model)
    (additional : List (CheckedAddressedNumberSource model)) : Nat :=
  additional.foldl (fun scale source => max scale source.source.info.scale)
    (max pair.left.source.info.scale pair.right.source.info.scale)

structure CheckedAddressedNumberExtremum (model : FlatModel) where
  private mk ::
  pair : CheckedAddressedNumberPair model
  additional : List (CheckedAddressedNumberSource model)
  additionalSameTarget :
    ∀ source ∈ additional,
      pair.left.placement.targetField = source.placement.targetField
  op : NumericExtremumOp
  sameScale :
    pair.left.placement.targetPolicy.info.scale =
      addressedNumberExtremumResultScale pair additional

def checkAddressedNumberExtremumList
    (model : FlatModel) (declaringGroup : GroupPath) (targetField : FieldId)
    (leftReference rightReference : SurfaceFieldPath)
    (additionalReferences : List SurfaceFieldPath)
    (op : NumericExtremumOp) :
    Except AddressedNumberExtremumElabError
      (CheckedAddressedNumberExtremum model) := do
  let pair ←
    checkAddressedNumberPair model declaringGroup targetField
      leftReference rightReference |>.mapError .pair
  let additional ←
    checkAdditionalNumberSources model declaringGroup targetField 3
      additionalReferences
  if hTargets : ∀ source ∈ additional,
      pair.left.placement.targetField = source.placement.targetField then
    let resultScale := addressedNumberExtremumResultScale pair additional
    if hScale : pair.left.placement.targetPolicy.info.scale = resultScale then
      pure {
        pair
        additional
        additionalSameTarget := hTargets
        op
        sameScale := hScale
      }
    else
      throw (.scaleMismatch pair.left.placement.targetPolicy.info.scale
        resultScale)
  else
    throw .incoherentAdditionalTarget

def checkAddressedNumberExtremum
    (model : FlatModel) (declaringGroup : GroupPath) (targetField : FieldId)
    (leftReference rightReference : SurfaceFieldPath)
    (op : NumericExtremumOp) :
    Except AddressedNumberExtremumElabError
      (CheckedAddressedNumberExtremum model) :=
  checkAddressedNumberExtremumList model declaringGroup targetField
    leftReference rightReference [] op

abbrev AddressedNumberExtremumFault := AddressedNumericLeafFault

namespace CheckedAddressedNumberExtremum

private def evaluateAdditionalAtPath (op : NumericExtremumOp)
    (input : CheckedDocument model) (path : List Nat) :
    List (CheckedAddressedNumberSource model) → NumericComputationResult →
      Except AddressedNumberExtremumFault NumericComputationResult
  | [], result => pure result
  | _, .poison cause => pure (.poison cause)
  | source :: rest, result => do
      let next ← source.evaluateAtPath input path
      evaluateAdditionalAtPath op input path rest
        (op.selectComputationResult result next)

private def evaluateAtPath
    (operation : CheckedAddressedNumberExtremum model)
    (input : CheckedDocument model) (path : List Nat) :
    Except AddressedNumberExtremumFault NumericComputationResult := do
  let initial ← operation.pair.evaluateAtPathWith input
    operation.op.selectComputationResult path
  evaluateAdditionalAtPath operation.op input path operation.additional initial

def execute (operation : CheckedAddressedNumberExtremum model)
    (input : CheckedDocument model) :
    Except AddressedNumberExtremumFault
      (List (SourcedNumericTargetOutcome CellAddr)) :=
  operation.pair.left.placement.executeWithPath input
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
