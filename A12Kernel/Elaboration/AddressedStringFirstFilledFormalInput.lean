import A12Kernel.Elaboration.AddressedStringFirstFilledComputation
import A12Kernel.Elaboration.ComputationFormalInput

/-! # Checked formal inputs for addressed ordinary String `FirstFilledValue`

This boundary prepares the selected ordinary String index source once, executes the parent-local scan through that view, and retains eager findings independently from runtime reachability and declaration-owned target checking.
-/

namespace A12Kernel

/-- Failure while composing selected formal-input preparation with addressed ordinary String `FirstFilledValue`. -/
inductive AddressedStringFirstFilledCheckedResultFault where
  | formalInput (cause : ComputationFormalInputPlanError)
  | preliminary (cause : CheckedIndexPreliminaryError)
  | execution (formalErrorsInOperands : List ComputationFormalInputFinding)
      (cause : AddressedStringFirstFilledComputationFault)
  deriving Repr, DecidableEq

namespace CheckedAddressedStringFirstFilledComputation

/-- Bind the checked ordinary String star source and computed target to the shared eager inventory. -/
def formalInputPlan
    (operation : CheckedAddressedStringFirstFilledComputation model) :
    Except ComputationFormalInputPlanError
      (CheckedComputationFormalInputPlan model) :=
  checkComputationFormalInputPlan model [operation.source.declaration.id]
    [operation.targetField]

/-- Prepare the selected source once, retain every eager finding, and preserve lazy parent-local execution plus target checking through the prepared read. -/
def executeResultWithFormalInputs
    (operation : CheckedAddressedStringFirstFilledComputation model)
    (patterns : PreparedFlatStringPatterns model compilePattern)
    (input : CheckedDocument model) :
    Except AddressedStringFirstFilledCheckedResultFault
      (AddressedStringFirstFilledComputationRunView model
        ComputationFormalInputFinding) := do
  let plan ← operation.formalInputPlan |>.mapError .formalInput
  let prepared ← plan.prepare input |>.mapError .preliminary
  match operation.executeResultWithRead patterns input
      prepared.preliminary.readComputation prepared.formalErrorsInOperands with
  | .error cause =>
      .error (.execution prepared.formalErrorsInOperands cause)
  | .ok result => .ok result

end CheckedAddressedStringFirstFilledComputation

end A12Kernel
