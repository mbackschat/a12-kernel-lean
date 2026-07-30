import A12Kernel.Elaboration.AddressedNumericLeaf

/-! # Same-scope repeatable `RangeAsNumber`

This capsule admits one ordinary repeatable Number target whose sole expression is `RangeAsNumber` over a checked evaluated String declaration in the same repeatable scope. It specializes the shared addressed numeric placement with one exact 1-based inclusive interval and the existing scalar evaluator.
-/

namespace A12Kernel

/-- Fail-closed errors specific to the bounded addressed range conversion. -/
inductive AddressedRangeAsNumberElabError where
  | placement (cause : AddressedNumericPlacementElabError)
  | invalidRange (start finish : Nat)
  | sourceNotEvaluatedString (path : List String)
  | scaleMismatch (target source : Nat)
  deriving Repr, DecidableEq

/-- One exact same-scope repeatable String-range-to-Number operation certified against a validated model. -/
structure CheckedAddressedRangeAsNumber (model : FlatModel) where
  private mk ::
  placement : CheckedAddressedNumericPlacement model
  source : FlatStringField
  start : Nat
  finish : Nat
  sourceCertified :
    placement.sourceDeclaration.toStringValueField? = some source
  rangeValid : validStringRange start finish = true
  sameScale : placement.targetPolicy.info.scale = 0

/-- Validate the exact evaluated-String source, interval, and scale-0 assignment on the shared repeatable placement. -/
def checkAddressedRangeAsNumber
    (model : FlatModel) (declaringGroup : GroupPath) (targetField : FieldId)
    (sourceReference : SurfaceFieldPath) (start finish : Nat) :
    Except AddressedRangeAsNumberElabError
      (CheckedAddressedRangeAsNumber model) :=
  match checkAddressedNumericPlacement model declaringGroup
      targetField sourceReference with
  | .error cause => .error (.placement cause)
  | .ok placement =>
    if hRange : validStringRange start finish then
      match hSource :
          placement.sourceDeclaration.toStringValueField? with
      | none =>
          .error
            (.sourceNotEvaluatedString placement.sourceDeclaration.path)
      | some source =>
        if hScale : placement.targetPolicy.info.scale = 0 then
          .ok {
            placement
            source
            start
            finish
            sourceCertified := hSource
            rangeValid := hRange
            sameScale := hScale
          }
        else
          .error
            (.scaleMismatch placement.targetPolicy.info.scale 0)
    else
      .error (.invalidRange start finish)

abbrev AddressedRangeAsNumberFault := AddressedNumericLeafFault

namespace CheckedAddressedRangeAsNumber

private def evaluateSource
    (operation : CheckedAddressedRangeAsNumber model)
    (sourceCell : CheckedCell) :
    Except NumericComputationFault NumericComputationResult :=
  let context : ScalarComputationContext := {
    read := fun field =>
      if field == operation.placement.sourceDeclaration.id then
        sourceCell
      else
        malformedCheckedCell
  }
  context.readNumericComputationAtom
    (.stringRange operation.source operation.start operation.finish)

/-- Execute the certified range conversion through the shared addressed placement. -/
def execute (operation : CheckedAddressedRangeAsNumber model)
    (input : CheckedDocument model) :
    Except AddressedRangeAsNumberFault
      (List (SourcedNumericTargetOutcome CellAddr)) :=
  operation.placement.executeWith input operation.evaluateSource

/-- Classify the addressed rich outcomes against the immutable source document without collapsing their exact row keys. -/
def executeResult
    (operation : CheckedAddressedRangeAsNumber model)
    (input : CheckedDocument model)
    (payloadAt : CellAddr → Payload)
    (supplied : List (ComputationFormalMessage Payload)) :
    Except AddressedRangeAsNumberFault
      (NumericComputationRunView
        (ComputationFormalMessage Payload) CellAddr) :=
  operation.placement.executeResultWith input operation.evaluateSource
    payloadAt supplied

end CheckedAddressedRangeAsNumber

end A12Kernel
