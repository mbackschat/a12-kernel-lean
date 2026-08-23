import A12Kernel.Elaboration.AddressedNumericLeaf

/-! # Same-scope repeatable DateRange-endpoint component

One numeric Date component of a selected DateRange endpoint, computed per row into a repeatable
Number target through the shared addressed numeric placement and the scalar computation evaluator.
The component's own admission rule and its cross-carrier read already belong to the endpoint-component
owner; what this module adds is the target half — a repeatable Number target at the source's own
scope and the measured derived-scale gate, which is scale 0 because every date component is an
integer.
-/

namespace A12Kernel

/-- Fail-closed errors specific to the bounded addressed endpoint-component operation. -/
inductive AddressedDateRangeBoundPartElabError where
  | placement (cause : AddressedNumericPlacementElabError)
  | componentNotExposed (path : List String) (part : DateNumericPart)
  | scaleMismatch (target source : Nat)
  deriving Repr, DecidableEq

namespace AddressedDateRangeBoundPartElabError

/-- Only the component refusal has a measured Kernel diagnostic; the derived-scale refusal reports
`MVK_INVALID_COMPARE_DEC_PLACES` at the Kernel but is not projected here, because this library error
does not distinguish the suppression branch that code also covers. -/
def diagnostic? :
    AddressedDateRangeBoundPartElabError → Option KernelStaticDiagnostic
  | .componentNotExposed _ _ => some .wrongDateFormatForOp
  | .placement _ | .scaleMismatch _ _ => none

end AddressedDateRangeBoundPartElabError

/-- One same-scope repeatable endpoint-component operation certified against a validated model. The
source field is derived from the placement rather than carried, because a `DATE_RANGE` reference is
determined by its declaration and the exposure certificate already re-derives the checked profile. -/
structure CheckedAddressedDateRangeBoundPart (model : FlatModel) where
  private mk ::
  placement : CheckedAddressedNumericPlacement model
  bound : DateRangeBound
  part : DateNumericPart
  componentExposed :
    model.exposesDateRangeBoundPart
      ({ id := placement.sourceDeclaration.id } : FlatDateRangeField) part = true
  sameScale : placement.targetPolicy.info.scale = 0

namespace CheckedAddressedDateRangeBoundPart

/-- The certified DateRange source, which is the placement's own source declaration. -/
def source (operation : CheckedAddressedDateRangeBoundPart model) :
    FlatDateRangeField := { id := operation.placement.sourceDeclaration.id }

end CheckedAddressedDateRangeBoundPart

/-- Validate the component exposure and the scale-0 assignment on the shared repeatable placement. -/
def checkAddressedDateRangeBoundPart
    (model : FlatModel) (declaringGroup : GroupPath) (targetField : FieldId)
    (sourceReference : SurfaceFieldPath) (bound : DateRangeBound)
    (part : DateNumericPart) :
    Except AddressedDateRangeBoundPartElabError
      (CheckedAddressedDateRangeBoundPart model) :=
  match checkAddressedNumericPlacement model declaringGroup
      targetField sourceReference with
  | .error cause => .error (.placement cause)
  | .ok placement =>
    if hExposed : model.exposesDateRangeBoundPart
        ({ id := placement.sourceDeclaration.id } : FlatDateRangeField)
        part = true then
      if hScale : placement.targetPolicy.info.scale = 0 then
        .ok {
          placement
          bound
          part
          componentExposed := hExposed
          sameScale := hScale
        }
      else
        .error (.scaleMismatch placement.targetPolicy.info.scale 0)
    else
      .error (.componentNotExposed placement.sourceDeclaration.path part)

abbrev AddressedDateRangeBoundPartFault := AddressedNumericLeafFault

namespace CheckedAddressedDateRangeBoundPart

private def evaluateSource
    (operation : CheckedAddressedDateRangeBoundPart model)
    (sourceCell : CheckedCell) :
    Except NumericComputationFault NumericComputationResult :=
  operation.placement.evaluateSourceAtom sourceCell
    (.dateRangeBoundPart operation.source operation.bound operation.part)

/-- Execute the certified component operation once per instantiated row through the shared placement. -/
def execute (operation : CheckedAddressedDateRangeBoundPart model)
    (input : CheckedDocument model) :
    Except AddressedDateRangeBoundPartFault
      (List (SourcedNumericTargetOutcome CellAddr)) :=
  operation.placement.executeWith input operation.evaluateSource

/-- Classify the addressed rich outcomes against the immutable source document without collapsing their exact row keys. -/
def executeResult
    (operation : CheckedAddressedDateRangeBoundPart model)
    (input : CheckedDocument model)
    (payloadAt : CellAddr → Payload)
    (supplied : List (ComputationFormalMessage Payload)) :
    Except AddressedDateRangeBoundPartFault
      (NumericComputationRunView
        (ComputationFormalMessage Payload) CellAddr) :=
  operation.placement.executeResultWith input operation.evaluateSource
    payloadAt supplied

end CheckedAddressedDateRangeBoundPart

end A12Kernel
