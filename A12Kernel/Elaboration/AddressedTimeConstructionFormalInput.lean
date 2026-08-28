import A12Kernel.Elaboration.TimeComputation
import A12Kernel.Elaboration.ComputationFormalInput

/-! # Checked formal inputs for addressed `Time(...)` construction -/

namespace A12Kernel

/-- Failure while composing direct formal-input collection with addressed Time construction. -/
inductive AddressedTimeConstructionCheckedResultFault where
  | formalInput (cause : ComputationFormalInputPlanError)
  | preliminary (cause : CheckedIndexPreliminaryError)
  | execution (formalErrorsInOperands : List ComputationFormalInputFinding)
      (cause : AddressedTimeConstructionFault)
  deriving Repr, DecidableEq

namespace CheckedAddressedTimeConstructionComputation

/-- Bind this checked construction's direct component fields and computed target to the shared eager inventory. -/
def formalInputPlan
    (operation : CheckedAddressedTimeConstructionComputation model) :
    Except ComputationFormalInputPlanError
      (CheckedComputationFormalInputPlan model) :=
  checkComputationFormalInputPlan model operation.fieldDependencies
    [operation.checkedTarget.targetField]

/-- Prepare the direct component view once, then execute and project the addressed Time result while retaining the eager inventory on later faults. -/
def executeResultWithFormalInputs
    (operation : CheckedAddressedTimeConstructionComputation model)
    (input : CheckedDocument model) :
    Except AddressedTimeConstructionCheckedResultFault
      (AddressedTimeConstructionRunView model ComputationFormalInputFinding) := do
  let plan ← operation.formalInputPlan |>.mapError .formalInput
  let prepared ← plan.prepare input |>.mapError .preliminary
  match operation.executeResultWithRead input
      prepared.preliminary.readComputation
      prepared.formalErrorsInOperands with
  | .ok view => pure view
  | .error cause => throw (.execution prepared.formalErrorsInOperands cause)

end CheckedAddressedTimeConstructionComputation

end A12Kernel
