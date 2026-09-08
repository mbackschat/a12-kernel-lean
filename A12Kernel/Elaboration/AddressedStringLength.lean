import A12Kernel.Elaboration.AddressedNumericLeaf

/-! # Repeatable String `Length` — one checked evaluated String source over the shared addressed numeric placement and scalar evaluator. -/

namespace A12Kernel

/-- Fail-closed errors specific to the bounded addressed String-length operation. -/
inductive AddressedStringLengthElabError where
  | placement (cause : AddressedNumericPlacementElabError)
  | sourceNotEvaluatedString (path : List String)
  | scaleMismatch (target source : Nat)
  deriving Repr, DecidableEq

/-- One repeatable String-length operation certified against a validated model. -/
structure CheckedAddressedStringLength (model : FlatModel) where
  private mk ::
  placement : CheckedAddressedNumericPlacement model
  source : FlatStringField
  sourceCertified :
    placement.sourceDeclaration.toStringValueField? = some source
  suppressExactScaleWarning : Bool
  scaleCertified : suppressExactScaleWarning = true ∨ placement.targetPolicy.info.scale = 0

/-- Validate the evaluated-String source and independently suppressible assignment-scale gate.
    The flag retains computation metadata for re-emission under the [numeric scale rule](../../spec/04-numbers-and-decimals.md#1-scale-gates----checked-at-parse-time). -/
def checkAddressedStringLength
    (model : FlatModel) (declaringGroup : GroupPath) (targetField : FieldId)
    (sourceReference : SurfaceFieldPath) (suppressExactScaleWarning : Bool := false) :
    Except AddressedStringLengthElabError
      (CheckedAddressedStringLength model) :=
  match checkAddressedNumericPlacement model declaringGroup
      targetField sourceReference with
  | .error cause => .error (.placement cause)
  | .ok placement =>
    match hSource :
        placement.sourceDeclaration.toStringValueField? with
    | none =>
        .error
          (.sourceNotEvaluatedString placement.sourceDeclaration.path)
    | some source =>
      if hScale : suppressExactScaleWarning = true ∨ placement.targetPolicy.info.scale = 0 then
        .ok {
          placement
          source
          sourceCertified := hSource
          suppressExactScaleWarning
          scaleCertified := hScale
        }
      else
        .error
          (.scaleMismatch placement.targetPolicy.info.scale 0)

abbrev AddressedStringLengthFault := AddressedNumericLeafFault

namespace CheckedAddressedStringLength

private def evaluateSource
    (operation : CheckedAddressedStringLength model)
    (sourceCell : CheckedCell) :
    Except NumericComputationFault NumericComputationResult :=
  operation.placement.evaluateSourceAtom sourceCell
    (.stringLength operation.source)

/-- Execute the certified String-length operation through the shared addressed placement. -/
def execute (operation : CheckedAddressedStringLength model)
    (input : CheckedDocument model) :
    Except AddressedStringLengthFault
      (List (SourcedNumericTargetOutcome CellAddr)) :=
  operation.placement.executeWith input operation.evaluateSource

/-- Classify the addressed rich outcomes against the immutable source document without collapsing their exact row keys. -/
def executeResult
    (operation : CheckedAddressedStringLength model)
    (input : CheckedDocument model)
    (payloadAt : CellAddr → Payload)
    (supplied : List (ComputationFormalMessage Payload)) :
    Except AddressedStringLengthFault
      (NumericComputationRunView
        (ComputationFormalMessage Payload) CellAddr) :=
  operation.placement.executeResultWith input operation.evaluateSource
    payloadAt supplied

end CheckedAddressedStringLength

end A12Kernel
