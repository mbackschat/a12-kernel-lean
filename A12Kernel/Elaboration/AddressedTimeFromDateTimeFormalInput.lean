import A12Kernel.Elaboration.AddressedTimeFromDateTime
import A12Kernel.Elaboration.ComputationFormalInput

/-! # Checked formal inputs for addressed `TimeFromDateTime` -/

namespace A12Kernel

/-- Failure while composing selected formal-input preparation with addressed Time extraction. -/
inductive AddressedTimeFromDateTimeCheckedResultFault where
  | formalInput (cause : ComputationFormalInputPlanError)
  | preliminary (cause : CheckedIndexPreliminaryError)
  | execution (formalErrorsInOperands : List ComputationFormalInputFinding)
      (cause : AddressedTimeFromDateTimeFault)
  deriving Repr, DecidableEq

namespace CheckedAddressedTimeFromDateTime

/-- The one complete-DateTime dependency used for scheduling and analysis. -/
def fieldDependencies (operation : CheckedAddressedTimeFromDateTime model) :
    List FieldId :=
  [operation.sourceBinding.source.id]

/-- Bind the direct source and computed Time target to the shared eager inventory. -/
def formalInputPlan (operation : CheckedAddressedTimeFromDateTime model) :
    Except ComputationFormalInputPlanError
      (CheckedComputationFormalInputPlan model) :=
  checkComputationFormalInputPlan model operation.fieldDependencies
    [operation.target.checked.target.id]

/-- Prepare the exact source view once, then execute and project the addressed Time result while retaining the eager inventory on later faults. -/
def executeResultWithFormalInputs
    (operation : CheckedAddressedTimeFromDateTime model)
    (input : CheckedDocument model) :
    Except AddressedTimeFromDateTimeCheckedResultFault
      (AddressedTimeFromDateTimeRunView model ComputationFormalInputFinding) := do
  let plan ← operation.formalInputPlan |>.mapError .formalInput
  let prepared ← plan.prepare input |>.mapError .preliminary
  match operation.executeResultWithRead input
      prepared.preliminary.readComputation
      prepared.formalErrorsInOperands with
  | .ok view => pure view
  | .error cause => throw (.execution prepared.formalErrorsInOperands cause)

end CheckedAddressedTimeFromDateTime

end A12Kernel
