import A12Kernel.Elaboration.AddressedNumericLeaf

/-! # Same-scope repeatable direct Number-field computation -/

namespace A12Kernel

/-- Fail-closed errors specific to direct addressed Number assignment. -/
inductive AddressedNumberFieldElabError where
  | placement (cause : AddressedNumericPlacementElabError)
  | sourceNotNumber (path : List String) (actual : SurfaceScalarKind)
  | scaleMismatch (target source : Nat)
  deriving Repr, DecidableEq

/-- One direct Number source and Number target certified at the same nonempty repeatable scope and exact scale. -/
structure CheckedAddressedNumberField (model : FlatModel) where
  private mk ::
  placement : CheckedAddressedNumericPlacement model
  source : FlatNumberField
  sourceCertified :
    placement.sourceDeclaration.toNumberField? = some source
  sameScale :
    placement.targetPolicy.info.scale = source.info.scale

/-- Validate the direct Number source and exact assignment scale on the shared addressed placement. -/
def checkAddressedNumberField
    (model : FlatModel) (declaringGroup : GroupPath) (targetField : FieldId)
    (sourceReference : SurfaceFieldPath) :
    Except AddressedNumberFieldElabError
      (CheckedAddressedNumberField model) :=
  match checkAddressedNumericPlacement model declaringGroup
      targetField sourceReference with
  | .error cause => .error (.placement cause)
  | .ok placement =>
    match hSource : placement.sourceDeclaration.toNumberField? with
    | none =>
        .error (.sourceNotNumber placement.sourceDeclaration.path
          placement.sourceDeclaration.policy.kind.surfaceKind)
    | some source =>
      if hScale :
          placement.targetPolicy.info.scale = source.info.scale then
        .ok { placement, source, sourceCertified := hSource, sameScale := hScale }
      else
        .error (.scaleMismatch placement.targetPolicy.info.scale source.info.scale)

abbrev AddressedNumberFieldFault := AddressedNumericLeafFault

namespace CheckedAddressedNumberField

private def evaluateSource
    (operation : CheckedAddressedNumberField model)
    (sourceCell : CheckedCell) :
    Except NumericComputationFault NumericComputationResult :=
  operation.placement.evaluateSourceAtom sourceCell
    (.field operation.placement.sourceDeclaration)

/-- Execute the certified direct Number read through the shared addressed placement. -/
def execute (operation : CheckedAddressedNumberField model)
    (input : CheckedDocument model) :
    Except AddressedNumberFieldFault
      (List (SourcedNumericTargetOutcome CellAddr)) :=
  operation.placement.executeWith input operation.evaluateSource

/-- Classify exact addressed outcomes against the immutable source document. -/
def executeResult
    (operation : CheckedAddressedNumberField model)
    (input : CheckedDocument model)
    (payloadAt : CellAddr → Payload)
    (supplied : List (ComputationFormalMessage Payload)) :
    Except AddressedNumberFieldFault
      (NumericComputationRunView
        (ComputationFormalMessage Payload) CellAddr) :=
  operation.placement.executeResultWith input operation.evaluateSource
    payloadAt supplied

end CheckedAddressedNumberField

end A12Kernel
