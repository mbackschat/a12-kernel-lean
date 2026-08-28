import A12Kernel.Elaboration.AddressedDateRangeBoundPart
import A12Kernel.Elaboration.NumericComputation.FormalInput

/-! # Checked formal inputs for addressed DateRange endpoint components -/

namespace A12Kernel

/-- Failure while composing selected formal-input preparation with addressed DateRange endpoint-component execution. -/
inductive AddressedDateRangeBoundPartCheckedResultFault where
  | formalInput (cause : ComputationFormalInputPlanError)
  | preliminary (cause : CheckedIndexPreliminaryError)
  | execution (formalErrorsInOperands : List ComputationFormalInputFinding)
      (cause : AddressedDateRangeBoundPartFault)
  deriving Repr, DecidableEq

namespace CheckedAddressedDateRangeBoundPart

/-- The one DateRange dependency used for scheduling and eager formal-input collection. -/
def fieldDependencies
    (operation : CheckedAddressedDateRangeBoundPart model) :
    List FieldId :=
  [operation.source.id]

/-- Bind the direct DateRange source and computed Number target to the shared eager inventory. -/
def formalInputPlan
    (operation : CheckedAddressedDateRangeBoundPart model) :
    Except ComputationFormalInputPlanError
      (CheckedComputationFormalInputPlan model) :=
  checkComputationFormalInputPlan model operation.fieldDependencies
    [operation.placement.targetField]

/-- Prepare the selected source once, execute through that exact view, and retain raw findings outside the typed Number message channel. -/
def executeResultWithFormalInputs
    (operation : CheckedAddressedDateRangeBoundPart model)
    (input : CheckedDocument model) :
    Except AddressedDateRangeBoundPartCheckedResultFault
      (NumericComputationFormalInputRunView model CellAddr) := do
  let plan ← operation.formalInputPlan |>.mapError .formalInput
  let prepared ← plan.prepare input |>.mapError .preliminary
  match operation.executeResultWithRead input
      prepared.preliminary.readComputation (fun _ => ()) [] with
  | .error cause =>
      .error (.execution prepared.formalErrorsInOperands cause)
  | .ok numeric =>
      .ok (NumericComputationFormalInputRunView.of numeric
        prepared.formalErrorsInOperands)

end CheckedAddressedDateRangeBoundPart

end A12Kernel
