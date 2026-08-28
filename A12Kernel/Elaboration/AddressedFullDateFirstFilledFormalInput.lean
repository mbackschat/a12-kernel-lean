import A12Kernel.Elaboration.AddressedFullDateFirstFilledComputation
import A12Kernel.Elaboration.ComputationFormalInput

/-! # Checked formal inputs for addressed FULL Date `FirstFilledValue`

This boundary prepares the selected full-Date index source once, executes the parent-local instant scan through that view, and retains eager findings independently from runtime reachability and target rendering.
-/

namespace A12Kernel

/-- Failure while composing selected formal-input preparation with addressed FULL Date `FirstFilledValue`. -/
inductive AddressedFullDateFirstFilledCheckedResultFault where
  | formalInput (cause : ComputationFormalInputPlanError)
  | preliminary (cause : CheckedIndexPreliminaryError)
  | execution (formalErrorsInOperands : List ComputationFormalInputFinding)
      (cause : AddressedFullDateFirstFilledComputationFault)
  deriving Repr, DecidableEq

namespace CheckedAddressedFullDateFirstFilledComputation

/-- Bind the checked full-Date star source and computed target to the shared eager inventory. -/
def formalInputPlan
    (operation : CheckedAddressedFullDateFirstFilledComputation model) :
    Except ComputationFormalInputPlanError
      (CheckedComputationFormalInputPlan model) :=
  checkComputationFormalInputPlan model [operation.source.declaration.id]
    [operation.targetField]

/-- Prepare the selected source once, retain every eager finding, and preserve lazy parent-local execution through the prepared read. -/
def executeResultWithFormalInputs
    (operation : CheckedAddressedFullDateFirstFilledComputation model)
    (input : CheckedDocument model) :
    Except AddressedFullDateFirstFilledCheckedResultFault
      (AddressedFullDateFirstFilledComputationRunView model
        ComputationFormalInputFinding) := do
  let plan ← operation.formalInputPlan |>.mapError .formalInput
  let prepared ← plan.prepare input |>.mapError .preliminary
  match operation.executeResultWithRead input
      prepared.preliminary.readComputation prepared.formalErrorsInOperands with
  | .error cause =>
      .error (.execution prepared.formalErrorsInOperands cause)
  | .ok result => .ok result

end CheckedAddressedFullDateFirstFilledComputation

end A12Kernel
