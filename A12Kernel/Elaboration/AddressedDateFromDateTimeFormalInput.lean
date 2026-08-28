import A12Kernel.Elaboration.AddressedDateFromDateTime
import A12Kernel.Elaboration.ComputationFormalInput

/-! # Checked formal inputs for addressed `DateFromDateTime` -/

namespace A12Kernel

/-- Failure while composing direct formal-input collection with addressed date extraction. -/
inductive AddressedDateFromDateTimeCheckedResultFault where
  | formalInput (cause : ComputationFormalInputPlanError)
  | preliminary (cause : CheckedIndexPreliminaryError)
  | execution (formalErrorsInOperands : List ComputationFormalInputFinding)
      (cause : AddressedDateFromDateTimeFault)
  deriving Repr, DecidableEq

namespace CheckedAddressedDateFromDateTime

/-- The one direct complete-DateTime dependency used for scheduling and analysis. -/
def fieldDependencies (operation : CheckedAddressedDateFromDateTime model) :
    List FieldId :=
  [operation.sourceBinding.source.id]

/-- Bind the direct source and computed FullDate target to the shared eager inventory. -/
def formalInputPlan (operation : CheckedAddressedDateFromDateTime model) :
    Except ComputationFormalInputPlanError
      (CheckedComputationFormalInputPlan model) :=
  checkComputationFormalInputPlan model operation.fieldDependencies
    [operation.target.checked.target.id]

/-- Prepare the exact source view once, then execute and project the addressed FullDate result while retaining the eager inventory on later faults. -/
def executeResultWithFormalInputs
    (operation : CheckedAddressedDateFromDateTime model)
    (input : CheckedDocument model) :
    Except AddressedDateFromDateTimeCheckedResultFault
      (AddressedDateFromDateTimeRunView model ComputationFormalInputFinding) := do
  let plan ← operation.formalInputPlan |>.mapError .formalInput
  let prepared ← plan.prepare input |>.mapError .preliminary
  match operation.executeResultWithRead input
      prepared.preliminary.readComputation
      prepared.formalErrorsInOperands with
  | .ok view => pure view
  | .error cause => throw (.execution prepared.formalErrorsInOperands cause)

end CheckedAddressedDateFromDateTime

end A12Kernel
