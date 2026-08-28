import A12Kernel.Elaboration.AddressedDateFragmentFirstFilledComputation
import A12Kernel.Elaboration.ComputationFormalInput

/-! # Checked formal inputs for addressed DateFragment `FirstFilledValue`

This boundary prepares the selected partial-Date index source once, executes the parent-local exact-token scan through that view, and retains eager findings independently from runtime reachability.
-/

namespace A12Kernel

/-- Failure while composing selected formal-input preparation with addressed DateFragment `FirstFilledValue`. -/
inductive AddressedDateFragmentFirstFilledCheckedResultFault where
  | formalInput (cause : ComputationFormalInputPlanError)
  | preliminary (cause : CheckedIndexPreliminaryError)
  | execution (formalErrorsInOperands : List ComputationFormalInputFinding)
      (cause : AddressedDateFragmentFirstFilledComputationFault)
  deriving Repr, DecidableEq

namespace CheckedAddressedDateFragmentFirstFilledComputation

/-- Bind the checked DateFragment star source and computed target to the shared eager inventory. -/
def formalInputPlan
    (operation : CheckedAddressedDateFragmentFirstFilledComputation model) :
    Except ComputationFormalInputPlanError
      (CheckedComputationFormalInputPlan model) :=
  checkComputationFormalInputPlan model [operation.source.declaration.id]
    [operation.targetField]

/-- Prepare the selected source once, retain every eager finding, and preserve lazy parent-local execution through the prepared read. -/
def executeResultWithFormalInputs
    (operation : CheckedAddressedDateFragmentFirstFilledComputation model)
    (input : CheckedDocument model) :
    Except AddressedDateFragmentFirstFilledCheckedResultFault
      (AddressedDateFragmentFirstFilledComputationRunView model
        ComputationFormalInputFinding) := do
  let plan ← operation.formalInputPlan |>.mapError .formalInput
  let prepared ← plan.prepare input |>.mapError .preliminary
  match operation.executeResultWithRead input
      prepared.preliminary.readComputation prepared.formalErrorsInOperands with
  | .error cause =>
      .error (.execution prepared.formalErrorsInOperands cause)
  | .ok result => .ok result

end CheckedAddressedDateFragmentFirstFilledComputation

end A12Kernel
