import A12Kernel.Elaboration.AddressedDateTimeFirstFilledComputation
import A12Kernel.Elaboration.ComputationFormalInput

/-! # Checked formal inputs for addressed DateTime `FirstFilledValue`

This boundary prepares the selected DateTime index source once, executes the parent-local instant scan through that view, and retains eager findings independently from runtime reachability, cached wall labels, and model-zone target rendering.
-/

namespace A12Kernel

/-- Failure while composing selected formal-input preparation with addressed DateTime `FirstFilledValue`. -/
inductive AddressedDateTimeFirstFilledCheckedResultFault where
  | formalInput (cause : ComputationFormalInputPlanError)
  | preliminary (cause : CheckedIndexPreliminaryError)
  | execution (formalErrorsInOperands : List ComputationFormalInputFinding)
      (cause : AddressedDateTimeFirstFilledComputationFault)
  deriving Repr, DecidableEq

namespace CheckedAddressedDateTimeFirstFilledComputation

/-- Bind the checked DateTime star source and computed target to the shared eager inventory. -/
def formalInputPlan
    (operation : CheckedAddressedDateTimeFirstFilledComputation model) :
    Except ComputationFormalInputPlanError
      (CheckedComputationFormalInputPlan model) :=
  checkComputationFormalInputPlan model [operation.source.declaration.id]
    [operation.targetField]

/-- Prepare the selected source once, retain every eager finding, and preserve lazy parent-local execution through the prepared read. -/
def executeResultWithFormalInputs
    (operation : CheckedAddressedDateTimeFirstFilledComputation model)
    (input : CheckedDocument model) :
    Except AddressedDateTimeFirstFilledCheckedResultFault
      (AddressedDateTimeFirstFilledComputationRunView model
        ComputationFormalInputFinding) := do
  let plan ← operation.formalInputPlan |>.mapError .formalInput
  let prepared ← plan.prepare input |>.mapError .preliminary
  match operation.executeResultWithRead input
      prepared.preliminary.readComputation prepared.formalErrorsInOperands with
  | .error cause =>
      .error (.execution prepared.formalErrorsInOperands cause)
  | .ok result => .ok result

end CheckedAddressedDateTimeFirstFilledComputation

end A12Kernel
