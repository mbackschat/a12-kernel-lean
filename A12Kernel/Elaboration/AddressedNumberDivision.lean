import A12Kernel.Elaboration.AddressedNumberField

/-! # Repeatable direct-Number division

This capsule retains two ordered checked Number sources and the required assignment-scale suppression, delegates quotient evaluation to the existing precision-50 semantics, and selects the existing warning-suppressed target checker at one exact addressed boundary.
-/

namespace A12Kernel

inductive AddressedNumberDivisionElabError where
  | pair (cause : AddressedNumberPairElabError)
  | scaleSuppressionRequired
  deriving Repr, DecidableEq

structure CheckedAddressedNumberDivision (model : FlatModel) where
  private mk ::
  pair : CheckedAddressedNumberPair model
  suppressExactScaleWarning : Bool
  suppressionCertified : suppressExactScaleWarning = true

def checkAddressedNumberDivision
    (model : FlatModel) (declaringGroup : GroupPath) (targetField : FieldId)
    (leftReference rightReference : SurfaceFieldPath)
    (suppressExactScaleWarning : Bool) :
    Except AddressedNumberDivisionElabError
      (CheckedAddressedNumberDivision model) := do
  let pair ←
    checkAddressedNumberPair model declaringGroup targetField
      leftReference rightReference |>.mapError .pair
  if hSuppression : suppressExactScaleWarning = true then
    pure { pair, suppressExactScaleWarning, suppressionCertified := hSuppression }
  else
    throw .scaleSuppressionRequired

abbrev AddressedNumberDivisionFault := AddressedNumericLeafFault

namespace CheckedAddressedNumberDivision

private def combine (left right : NumericComputationResult) :
    NumericComputationResult :=
  NumericComputationResult.combineReached
    (fun leftValue rightValue =>
      NumericComputationResult.ofArithmetic (divideNumeric leftValue rightValue))
    left right

def execute (operation : CheckedAddressedNumberDivision model)
    (input : CheckedDocument model) :
    Except AddressedNumberDivisionFault
      (List (SourcedNumericTargetOutcome CellAddr)) :=
  operation.pair.executeWithScaleWarningSuppressed input combine

def executeResult
    (operation : CheckedAddressedNumberDivision model)
    (input : CheckedDocument model)
    (payloadAt : CellAddr → Payload)
    (supplied : List (ComputationFormalMessage Payload)) :
    Except AddressedNumberDivisionFault
      (NumericComputationRunView
        (ComputationFormalMessage Payload) CellAddr) :=
  operation.pair.executeResultWithScaleWarningSuppressed input
    combine payloadAt supplied

end CheckedAddressedNumberDivision

end A12Kernel
