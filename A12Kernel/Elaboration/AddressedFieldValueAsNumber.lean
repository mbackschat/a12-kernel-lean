import A12Kernel.Elaboration.AddressedNumericLeaf

/-! # Same-scope repeatable `FieldValueAsNumber`

This capsule admits one ordinary repeatable Number target whose sole expression is `FieldValueAsNumber` over a checked String, stored Enumeration, or Enumeration-category declaration in the same repeatable scope. It specializes the shared addressed numeric placement with the certified conversion source and existing scalar evaluator.

Other numeric expressions, guards, cascades, and scheduling remain separate.
-/

namespace A12Kernel

/-- Fail-closed errors specific to the bounded addressed conversion. -/
inductive AddressedFieldValueAsNumberElabError where
  | placement (cause : AddressedNumericPlacementElabError)
  | sourceKindMismatch (path : List String) (actual : SurfaceScalarKind)
  | sourceNotConvertible (path : List String)
  | scaleMismatch (target source : Nat)
  deriving Repr, DecidableEq

/-- One exact same-scope repeatable textual-to-Number operation certified against a validated model. -/
structure CheckedAddressedFieldValueAsNumber (model : FlatModel) where
  private mk ::
  placement : CheckedAddressedNumericPlacement model
  projectionRef : EnumerationProjectionRef
  source : ResolvedFieldValueAsNumberSource
  sourceCertified :
    placement.sourceDeclaration.resolveFieldValueAsNumberSource
        projectionRef = .ok source
  sameScale : source.scale = placement.targetPolicy.info.scale

/-- Validate the exact conversion source and assignment scale on the shared repeatable placement. -/
def checkAddressedFieldValueAsNumber
    (model : FlatModel) (declaringGroup : GroupPath) (targetField : FieldId)
    (sourceReference : SurfaceTextFieldOperand) :
    Except AddressedFieldValueAsNumberElabError
      (CheckedAddressedFieldValueAsNumber model) :=
  match checkAddressedNumericPlacement model declaringGroup
      targetField sourceReference.reference with
  | .error cause => .error (.placement cause)
  | .ok placement =>
    match placement.sourceDeclaration.policy.kind with
    | .string | .enumeration =>
      match hSourceCertified :
          placement.sourceDeclaration.resolveFieldValueAsNumberSource
            sourceReference.projectionRef with
      | .error _ =>
          .error
            (.sourceNotConvertible placement.sourceDeclaration.path)
      | .ok source =>
        if hScale :
            source.scale = placement.targetPolicy.info.scale then
          .ok {
            placement
            projectionRef := sourceReference.projectionRef
            source
            sourceCertified := hSourceCertified
            sameScale := hScale
          }
        else
          .error (.scaleMismatch
            placement.targetPolicy.info.scale source.scale)
    | actual =>
        .error (.sourceKindMismatch
          placement.sourceDeclaration.path actual.surfaceKind)

abbrev AddressedFieldValueAsNumberFault := AddressedNumericLeafFault

namespace CheckedAddressedFieldValueAsNumber

private def evaluateSource
    (operation : CheckedAddressedFieldValueAsNumber model)
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
    (.fieldValueAsNumber operation.source)

/-- Execute the certified conversion through the shared addressed placement. -/
def execute (operation : CheckedAddressedFieldValueAsNumber model)
    (input : CheckedDocument model) :
    Except AddressedFieldValueAsNumberFault
      (List (SourcedNumericTargetOutcome CellAddr)) :=
  operation.placement.executeWith input operation.evaluateSource

/-- Classify the addressed rich outcomes against the immutable source document without collapsing their exact row keys. -/
def executeResult
    (operation : CheckedAddressedFieldValueAsNumber model)
    (input : CheckedDocument model)
    (payloadAt : CellAddr → Payload)
    (supplied : List (ComputationFormalMessage Payload)) :
    Except AddressedFieldValueAsNumberFault
      (NumericComputationRunView
        (ComputationFormalMessage Payload) CellAddr) :=
  operation.placement.executeResultWith input operation.evaluateSource
    payloadAt supplied

end CheckedAddressedFieldValueAsNumber

end A12Kernel
