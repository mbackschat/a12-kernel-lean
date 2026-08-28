import A12Kernel.Elaboration.AddressedTimeFirstFilledComputation
import A12Kernel.Elaboration.ComputationFormalInput

/-! # Checked formal inputs for addressed Time `FirstFilledValue`

This boundary prepares the selected Time index source once, executes the parent-local clock scan through that view, and retains eager findings independently from runtime reachability, transport instants, and target rendering.
-/

namespace A12Kernel

/-- Failure while composing selected formal-input preparation with addressed Time `FirstFilledValue`. -/
inductive AddressedTimeFirstFilledCheckedResultFault where
  | formalInput (cause : ComputationFormalInputPlanError)
  | preliminary (cause : CheckedIndexPreliminaryError)
  | execution (formalErrorsInOperands : List ComputationFormalInputFinding)
      (cause : AddressedTimeFirstFilledComputationFault)
  deriving Repr, DecidableEq

namespace CheckedAddressedTimeFirstFilledComputation

/-- Bind the checked Time star source and computed target to the shared eager inventory. -/
def formalInputPlan
    (operation : CheckedAddressedTimeFirstFilledComputation model) :
    Except ComputationFormalInputPlanError
      (CheckedComputationFormalInputPlan model) :=
  checkComputationFormalInputPlan model [operation.source.declaration.id]
    [operation.targetField]

/-- Prepare the selected source once, retain every eager finding, and preserve lazy parent-local execution through the prepared read. -/
def executeResultWithFormalInputs
    (operation : CheckedAddressedTimeFirstFilledComputation model)
    (input : CheckedDocument model) :
    Except AddressedTimeFirstFilledCheckedResultFault
      (AddressedTimeFirstFilledComputationRunView model
        ComputationFormalInputFinding) := do
  let plan ← operation.formalInputPlan |>.mapError .formalInput
  let prepared ← plan.prepare input |>.mapError .preliminary
  match operation.executeResultWithRead input
      prepared.preliminary.readComputation prepared.formalErrorsInOperands with
  | .error cause =>
      .error (.execution prepared.formalErrorsInOperands cause)
  | .ok result => .ok result

end CheckedAddressedTimeFirstFilledComputation

end A12Kernel
