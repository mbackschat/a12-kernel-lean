import A12Kernel.Elaboration.AddressedEnumerationComputation
import A12Kernel.Elaboration.ComputationFormalInput

/-! # Checked formal inputs for addressed Enumeration assignment -/

namespace A12Kernel

/-- Failure while composing direct formal-input collection with addressed Enumeration assignment. -/
inductive AddressedEnumerationCheckedResultFault where
  | formalInput (cause : ComputationFormalInputPlanError)
  | execution (cause : AddressedEnumerationComputationFault)
  deriving Repr, DecidableEq

namespace CheckedAddressedEnumerationComputation

/-- Bind the literal-or-field source and computed Enumeration target to the shared eager inventory. -/
def formalInputPlan (operation : CheckedAddressedEnumerationComputation model) :
    Except ComputationFormalInputPlanError
      (CheckedComputationFormalInputPlan model) :=
  checkComputationFormalInputPlan model operation.source.fieldDependencies
    [operation.target.field]

/-- Collect source findings eagerly, then execute and project the addressed String-shaped result. -/
def executeResultWithFormalInputs
    (operation : CheckedAddressedEnumerationComputation model)
    (input : CheckedDocument model) :
    Except AddressedEnumerationCheckedResultFault
      (AddressedEnumerationComputationRunView model ComputationFormalInputFinding) := do
  let plan ← operation.formalInputPlan |>.mapError .formalInput
  operation.executeResult input (plan.findings input) |>.mapError .execution

end CheckedAddressedEnumerationComputation

end A12Kernel
