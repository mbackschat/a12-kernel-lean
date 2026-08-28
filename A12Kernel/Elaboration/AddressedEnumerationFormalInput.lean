import A12Kernel.Elaboration.AddressedEnumerationComputation
import A12Kernel.Elaboration.ComputationFormalInput

/-! # Checked formal inputs for addressed Enumeration assignment -/

namespace A12Kernel

/-- Failure while composing selected formal-input preparation with addressed Enumeration assignment. -/
inductive AddressedEnumerationCheckedResultFault where
  | formalInput (cause : ComputationFormalInputPlanError)
  | preliminary (cause : CheckedIndexPreliminaryError)
  | execution (formalErrorsInOperands : List ComputationFormalInputFinding)
      (cause : AddressedEnumerationComputationFault)
  deriving Repr, DecidableEq

namespace CheckedAddressedEnumerationComputation

/-- Bind the literal-or-field source and computed Enumeration target to the shared eager inventory. -/
def formalInputPlan (operation : CheckedAddressedEnumerationComputation model) :
    Except ComputationFormalInputPlanError
      (CheckedComputationFormalInputPlan model) :=
  checkComputationFormalInputPlan model operation.source.fieldDependencies
    [operation.target.field]

/-- Prepare selected source findings and index state once, then execute through that exact view and retain the inventory beside either result arm. -/
def executeResultWithFormalInputs
    (operation : CheckedAddressedEnumerationComputation model)
    (input : CheckedDocument model) :
    Except AddressedEnumerationCheckedResultFault
      (AddressedEnumerationComputationRunView model ComputationFormalInputFinding) := do
  let plan ← operation.formalInputPlan |>.mapError .formalInput
  let prepared ← plan.prepare input |>.mapError .preliminary
  match operation.executeResultWithRead input
      prepared.preliminary.readComputation prepared.formalErrorsInOperands with
  | .error cause =>
      .error (.execution prepared.formalErrorsInOperands cause)
  | .ok result => .ok result

end CheckedAddressedEnumerationComputation

end A12Kernel
