import A12Kernel.Elaboration.AddressedCustomFirstFilledComputation
import A12Kernel.Elaboration.ComputationFormalInput

/-! # Checked formal inputs for addressed Custom `FirstFilledValue`

This boundary prepares the selected Custom index source once, preserves its already-checked registered-validator result, executes the parent-local scan through that view, and retains eager generated findings independently from runtime reachability.
-/

namespace A12Kernel

/-- Failure while composing selected formal-input preparation with addressed Custom `FirstFilledValue`. -/
inductive AddressedCustomFirstFilledCheckedResultFault where
  | formalInput (cause : ComputationFormalInputPlanError)
  | preliminary (cause : CheckedIndexPreliminaryError)
  | execution (formalErrorsInOperands : List ComputationFormalInputFinding)
      (cause : AddressedCustomFirstFilledComputationFault)
  deriving Repr, DecidableEq

namespace CheckedAddressedCustomFirstFilledComputation

/-- Bind the checked Custom star source and computed target to the shared eager inventory. -/
def formalInputPlan
    (operation : CheckedAddressedCustomFirstFilledComputation model) :
    Except ComputationFormalInputPlanError
      (CheckedComputationFormalInputPlan model) :=
  checkComputationFormalInputPlan model [operation.source.declaration.id]
    [operation.targetField]

/-- Prepare the selected source once, retain every eager finding, and preserve parent-local Custom selection through the prepared read. -/
def executeResultWithFormalInputs
    (operation : CheckedAddressedCustomFirstFilledComputation model)
    (input : CheckedDocument model) :
    Except AddressedCustomFirstFilledCheckedResultFault
      (AddressedCustomFirstFilledComputationRunView model
        ComputationFormalInputFinding) := do
  let plan ← operation.formalInputPlan |>.mapError .formalInput
  let prepared ← plan.prepare input |>.mapError .preliminary
  match operation.executeResultWithRead input
      prepared.preliminary.readComputation prepared.formalErrorsInOperands with
  | .error cause =>
      .error (.execution prepared.formalErrorsInOperands cause)
  | .ok result => .ok result

end CheckedAddressedCustomFirstFilledComputation

end A12Kernel
