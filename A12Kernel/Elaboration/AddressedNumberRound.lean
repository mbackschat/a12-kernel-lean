import A12Kernel.Elaboration.AddressedNumberField

/-! # Repeatable direct-Number rounding

This capsule reuses the shared checked Number source and scalar rounding semantics. Its only new static fact is that the target scale equals the authored rounding places.
-/

namespace A12Kernel

/-- Fail-closed errors specific to addressed direct-Number rounding. -/
inductive AddressedNumberRoundElabError where
  | source (cause : AddressedNumberSourceElabError)
  | scaleMismatch (target result : Nat)
  deriving Repr, DecidableEq

/-- One addressed Number source plus an admitted rounding mode and exact result scale. -/
structure CheckedAddressedNumberRound (model : FlatModel) where
  private mk ::
  numberSource : CheckedAddressedNumberSource model
  mode : DecimalRoundingMode
  places : RoundingPlaces
  sameScale :
    numberSource.placement.targetPolicy.info.scale = places.val

/-- Validate one rounding wrapper over the shared direct Number source. -/
def checkAddressedNumberRound
    (model : FlatModel) (declaringGroup : GroupPath) (targetField : FieldId)
    (sourceReference : SurfaceFieldPath) (mode : DecimalRoundingMode)
    (places : RoundingPlaces) :
    Except AddressedNumberRoundElabError
      (CheckedAddressedNumberRound model) :=
  match checkAddressedNumberSource model declaringGroup
      targetField sourceReference with
  | .error cause => .error (.source cause)
  | .ok numberSource =>
    if hScale : numberSource.placement.targetPolicy.info.scale = places.val then
      .ok { numberSource, mode, places, sameScale := hScale }
    else
      .error (.scaleMismatch numberSource.placement.targetPolicy.info.scale
        places.val)

abbrev AddressedNumberRoundFault := AddressedNumericLeafFault

namespace CheckedAddressedNumberRound

private def evaluateSource
    (operation : CheckedAddressedNumberRound model)
    (sourceCell : CheckedCell) :
    Except NumericComputationFault NumericComputationResult :=
  let atom : ResolvedNumericAtom FlatFieldDecl :=
    .field operation.numberSource.placement.sourceDeclaration
  let expression : LoweredNumericExpr (ResolvedNumericAtom FlatFieldDecl) :=
    .round operation.mode operation.places (.atom atom)
  expression.evalComputation
    (operation.numberSource.placement.evaluateSourceAtom sourceCell)

/-- Execute the certified rounding expression through the shared addressed placement. -/
def execute (operation : CheckedAddressedNumberRound model)
    (input : CheckedDocument model) :
    Except AddressedNumberRoundFault
      (List (SourcedNumericTargetOutcome CellAddr)) :=
  operation.numberSource.placement.executeWith input operation.evaluateSource

/-- Classify exact addressed outcomes against the immutable source document. -/
def executeResult
    (operation : CheckedAddressedNumberRound model)
    (input : CheckedDocument model)
    (payloadAt : CellAddr → Payload)
    (supplied : List (ComputationFormalMessage Payload)) :
    Except AddressedNumberRoundFault
      (NumericComputationRunView
        (ComputationFormalMessage Payload) CellAddr) :=
  operation.numberSource.placement.executeResultWith input operation.evaluateSource
    payloadAt supplied

end CheckedAddressedNumberRound

end A12Kernel
