import A12Kernel.Elaboration.AddressedNumberField

/-! # Repeatable direct-Number power

This capsule retains an ordered direct Number base and exponent, certifies the exponent's static scale-0 admission and the required result-scale suppression, delegates staged power evaluation to the existing scalar semantics, and selects the exact target placement's warning-suppressed checker.
-/

namespace A12Kernel

inductive AddressedNumberPowerElabError where
  | pair (cause : AddressedNumberPairElabError)
  | invalidExponentScale (actual : Nat)
  | scaleSuppressionRequired
  deriving Repr, DecidableEq

structure CheckedAddressedNumberPower (model : FlatModel) where
  private mk ::
  pair : CheckedAddressedNumberPair model
  exponentScaleZero : pair.right.source.info.scale = 0
  suppressExactScaleWarning : Bool
  suppressionCertified : suppressExactScaleWarning = true

def checkAddressedNumberPower
    (model : FlatModel) (declaringGroup : GroupPath) (targetField : FieldId)
    (baseReference exponentReference : SurfaceFieldPath)
    (suppressExactScaleWarning : Bool) :
    Except AddressedNumberPowerElabError
      (CheckedAddressedNumberPower model) := do
  let pair ←
    checkAddressedNumberPair model declaringGroup targetField
      baseReference exponentReference |>.mapError .pair
  if hExponent : pair.right.source.info.scale = 0 then
    if hSuppression : suppressExactScaleWarning = true then
      pure {
        pair
        exponentScaleZero := hExponent
        suppressExactScaleWarning
        suppressionCertified := hSuppression
      }
    else
      throw .scaleSuppressionRequired
  else
    throw (.invalidExponentScale pair.right.source.info.scale)

abbrev AddressedNumberPowerFault := AddressedNumericLeafFault

namespace CheckedAddressedNumberPower

def execute (operation : CheckedAddressedNumberPower model)
    (input : CheckedDocument model) :
    Except AddressedNumberPowerFault
      (List (SourcedNumericTargetOutcome CellAddr)) :=
  operation.pair.executeWithScaleWarningSuppressed input
    NumericComputationResult.evalPower

def executeResult
    (operation : CheckedAddressedNumberPower model)
    (input : CheckedDocument model)
    (payloadAt : CellAddr → Payload)
    (supplied : List (ComputationFormalMessage Payload)) :
    Except AddressedNumberPowerFault
      (NumericComputationRunView
        (ComputationFormalMessage Payload) CellAddr) :=
  operation.pair.executeResultWithScaleWarningSuppressed input
    NumericComputationResult.evalPower payloadAt supplied

end CheckedAddressedNumberPower

end A12Kernel
