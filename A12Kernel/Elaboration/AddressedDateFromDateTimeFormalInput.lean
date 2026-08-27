import A12Kernel.Elaboration.AddressedDateFromDateTime
import A12Kernel.Elaboration.ComputationFormalInput

/-! # Checked formal inputs for addressed `DateFromDateTime` -/

namespace A12Kernel

/-- Failure while composing direct formal-input collection with addressed date extraction. -/
inductive AddressedDateFromDateTimeCheckedResultFault where
  | formalInput (cause : ComputationFormalInputPlanError)
  | execution (cause : AddressedDateFromDateTimeFault)
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

/-- Collect the exact source findings eagerly, then execute and project the addressed FullDate result. -/
def executeResultWithFormalInputs
    (operation : CheckedAddressedDateFromDateTime model)
    (input : CheckedDocument model) :
    Except AddressedDateFromDateTimeCheckedResultFault
      (AddressedDateFromDateTimeRunView model ComputationFormalInputFinding) := do
  let plan ← operation.formalInputPlan |>.mapError .formalInput
  operation.executeResult input (plan.findings input) |>.mapError .execution

end CheckedAddressedDateFromDateTime

end A12Kernel
