import A12Kernel.Elaboration.AddressedNumberField

/-! # Same-scope repeatable direct-Number extrema

This capsule retains a nonempty ordered list of checked Number sources, delegates the authored-order fold to the existing scalar extrema semantics, and reuses the shared exact-address target owner.
-/

namespace A12Kernel

inductive AddressedNumberExtremumElabError where
  | source (position : Nat) (cause : AddressedNumberSourceElabError)
  | incoherentTarget
  | scaleMismatch (target result : Nat)
  deriving Repr, DecidableEq

private def checkNumberSources
    (model : FlatModel) (declaringGroup : GroupPath) (targetField : FieldId) :
    Nat → List SurfaceFieldPath →
      Except AddressedNumberExtremumElabError
        (List (CheckedAddressedNumberSource model))
  | _, [] => pure []
  | position, reference :: rest => do
      let source ←
        checkAddressedNumberSource model declaringGroup targetField reference
          |>.mapError (.source position)
      let tail ← checkNumberSources model declaringGroup targetField
        (position + 1) rest
      pure (source :: tail)

def addressedNumberExtremumResultScale
    (first : CheckedAddressedNumberSource model)
    (rest : List (CheckedAddressedNumberSource model)) : Nat :=
  rest.foldl (fun scale source => max scale source.source.info.scale)
    first.source.info.scale

structure CheckedAddressedNumberExtremum (model : FlatModel) where
  private mk ::
  first : CheckedAddressedNumberSource model
  rest : List (CheckedAddressedNumberSource model)
  restSameTarget :
    ∀ source ∈ rest,
      first.placement.targetField = source.placement.targetField
  op : NumericExtremumOp
  sameScale :
    first.placement.targetPolicy.info.scale =
      addressedNumberExtremumResultScale first rest

def checkAddressedNumberExtremumList
    (model : FlatModel) (declaringGroup : GroupPath) (targetField : FieldId)
    (firstReference : SurfaceFieldPath)
    (restReferences : List SurfaceFieldPath)
    (op : NumericExtremumOp) :
    Except AddressedNumberExtremumElabError
      (CheckedAddressedNumberExtremum model) := do
  let first ←
    checkAddressedNumberSource model declaringGroup targetField firstReference
      |>.mapError (.source 1)
  let rest ←
    checkNumberSources model declaringGroup targetField 2 restReferences
  if hTargets : ∀ source ∈ rest,
      first.placement.targetField = source.placement.targetField then
    let resultScale := addressedNumberExtremumResultScale first rest
    if hScale : first.placement.targetPolicy.info.scale = resultScale then
      pure {
        first
        rest
        restSameTarget := hTargets
        op
        sameScale := hScale
      }
    else
      throw (.scaleMismatch first.placement.targetPolicy.info.scale
        resultScale)
  else
    throw .incoherentTarget

def checkAddressedNumberExtremum
    (model : FlatModel) (declaringGroup : GroupPath) (targetField : FieldId)
    (leftReference rightReference : SurfaceFieldPath)
    (op : NumericExtremumOp) :
    Except AddressedNumberExtremumElabError
      (CheckedAddressedNumberExtremum model) :=
  checkAddressedNumberExtremumList model declaringGroup targetField
    leftReference [rightReference] op

abbrev AddressedNumberExtremumFault := AddressedNumericLeafFault

namespace CheckedAddressedNumberExtremum

private def evaluateRestAtPath (op : NumericExtremumOp)
    (input : CheckedDocument model) (path : List Nat) :
    List (CheckedAddressedNumberSource model) → NumericComputationResult →
      Except AddressedNumberExtremumFault NumericComputationResult
  | [], result => pure result
  | _, .poison cause => pure (.poison cause)
  | source :: rest, result => do
      let next ← source.evaluateAtPath input path
      evaluateRestAtPath op input path rest
        (op.selectComputationResult result next)

private def evaluateAtPath
    (operation : CheckedAddressedNumberExtremum model)
    (input : CheckedDocument model) (path : List Nat) :
    Except AddressedNumberExtremumFault NumericComputationResult := do
  let initial ← operation.first.evaluateAtPath input path
  evaluateRestAtPath operation.op input path operation.rest initial

def execute (operation : CheckedAddressedNumberExtremum model)
    (input : CheckedDocument model) :
    Except AddressedNumberExtremumFault
      (List (SourcedNumericTargetOutcome CellAddr)) :=
  operation.first.placement.executeWithPath input
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
