import A12Kernel.Elaboration.TimeComputation
import A12Kernel.Elaboration.ComputationFormalInput

/-! # Checked formal inputs for addressed `Time(...)` construction -/

namespace A12Kernel

/-- Failure while composing direct formal-input collection with addressed Time construction. -/
inductive AddressedTimeConstructionCheckedResultFault where
  | formalInput (cause : ComputationFormalInputPlanError)
  | execution (cause : AddressedTimeConstructionFault)
  deriving Repr, DecidableEq

namespace CheckedAddressedTimeConstructionComputation

/-- Bind this checked construction's direct component fields and computed target to the shared eager inventory. -/
def formalInputPlan
    (operation : CheckedAddressedTimeConstructionComputation model) :
    Except ComputationFormalInputPlanError
      (CheckedComputationFormalInputPlan model) :=
  checkComputationFormalInputPlan model operation.fieldDependencies
    [operation.checkedTarget.targetField]

/-- Collect direct component findings eagerly, then execute and project the addressed Time result. -/
def executeResultWithFormalInputs
    (operation : CheckedAddressedTimeConstructionComputation model)
    (input : CheckedDocument model) :
    Except AddressedTimeConstructionCheckedResultFault
      (AddressedTimeConstructionRunView model ComputationFormalInputFinding) := do
  let plan ← operation.formalInputPlan |>.mapError .formalInput
  operation.executeResult input (plan.findings input) |>.mapError .execution

end CheckedAddressedTimeConstructionComputation

end A12Kernel
