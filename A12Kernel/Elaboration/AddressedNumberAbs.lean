import A12Kernel.Elaboration.AddressedNumberField

/-! # Same-scope repeatable Number `Abs`

This capsule retains the already-certified direct Number source and target placement, then evaluates one absolute-value node through the existing scalar expression semantics. It introduces no second Number-source representation.
-/

namespace A12Kernel

/-- `Abs` has exactly the direct Number source's placement, kind, and scale admission failures. -/
abbrev AddressedNumberAbsElabError := AddressedNumberFieldElabError

/-- One addressed Number source certified for a scale-preserving absolute-value computation. -/
structure CheckedAddressedNumberAbs (model : FlatModel) where
  private mk ::
  numberSource : CheckedAddressedNumberField model

/-- Validate `Abs` through the shared direct Number source certificate. -/
def checkAddressedNumberAbs
    (model : FlatModel) (declaringGroup : GroupPath) (targetField : FieldId)
    (sourceReference : SurfaceFieldPath) :
    Except AddressedNumberAbsElabError (CheckedAddressedNumberAbs model) :=
  (checkAddressedNumberField model declaringGroup targetField sourceReference).map
    fun numberSource => { numberSource }

abbrev AddressedNumberAbsFault := AddressedNumericLeafFault

namespace CheckedAddressedNumberAbs

private def evaluateSource
    (operation : CheckedAddressedNumberAbs model)
    (sourceCell : CheckedCell) :
    Except NumericComputationFault NumericComputationResult :=
  let atom : ResolvedNumericAtom FlatFieldDecl :=
    .field operation.numberSource.placement.sourceDeclaration
  let expression : LoweredNumericExpr (ResolvedNumericAtom FlatFieldDecl) :=
    .abs (.atom atom)
  expression.evalComputation
    (operation.numberSource.placement.evaluateSourceAtom sourceCell)

/-- Execute the certified absolute-value expression through the shared addressed placement. -/
def execute (operation : CheckedAddressedNumberAbs model)
    (input : CheckedDocument model) :
    Except AddressedNumberAbsFault
      (List (SourcedNumericTargetOutcome CellAddr)) :=
  operation.numberSource.placement.executeWith input operation.evaluateSource

/-- Classify exact addressed outcomes against the immutable source document. -/
def executeResult
    (operation : CheckedAddressedNumberAbs model)
    (input : CheckedDocument model)
    (payloadAt : CellAddr → Payload)
    (supplied : List (ComputationFormalMessage Payload)) :
    Except AddressedNumberAbsFault
      (NumericComputationRunView
        (ComputationFormalMessage Payload) CellAddr) :=
  operation.numberSource.placement.executeResultWith input operation.evaluateSource
    payloadAt supplied

end CheckedAddressedNumberAbs

end A12Kernel
