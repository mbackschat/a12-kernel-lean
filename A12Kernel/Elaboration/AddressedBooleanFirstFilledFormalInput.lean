import A12Kernel.Elaboration.AddressedBooleanFirstFilledComputation
import A12Kernel.Elaboration.ComputationFormalInput

/-! # Checked formal inputs for addressed Boolean `FirstFilledValue`

This boundary prepares the selected Boolean index source once, executes the parent-local scan through that exact caller view, and retains eager input findings independently from runtime reachability.
-/

namespace A12Kernel

/-- Failure while composing selected formal-input preparation with addressed Boolean `FirstFilledValue`. -/
inductive AddressedBooleanFirstFilledCheckedResultFault where
  | formalInput (cause : ComputationFormalInputPlanError)
  | preliminary (cause : CheckedIndexPreliminaryError)
  | execution (formalErrorsInOperands : List ComputationFormalInputFinding)
      (cause : AddressedBooleanFirstFilledComputationFault)
  deriving Repr, DecidableEq

namespace CheckedAddressedBooleanFirstFilledComputation

/-- Bind the checked Boolean star source and computed target to the shared eager inventory. -/
def formalInputPlan
    (operation : CheckedAddressedBooleanFirstFilledComputation model) :
    Except ComputationFormalInputPlanError
      (CheckedComputationFormalInputPlan model) :=
  checkComputationFormalInputPlan model [operation.source.declaration.id]
    [operation.targetField]

/-- Prepare the selected source once, retain every eager finding, and preserve lazy parent-local execution through the prepared read. -/
def executeResultWithFormalInputs
    (operation : CheckedAddressedBooleanFirstFilledComputation model)
    (input : CheckedDocument model) :
    Except AddressedBooleanFirstFilledCheckedResultFault
      (AddressedBooleanFirstFilledComputationRunView model
        ComputationFormalInputFinding) := do
  let plan ← operation.formalInputPlan |>.mapError .formalInput
  let prepared ← plan.prepare input |>.mapError .preliminary
  match operation.executeResultWithRead input
      prepared.preliminary.readComputation prepared.formalErrorsInOperands with
  | .error cause =>
      .error (.execution prepared.formalErrorsInOperands cause)
  | .ok result => .ok result

end CheckedAddressedBooleanFirstFilledComputation

end A12Kernel
