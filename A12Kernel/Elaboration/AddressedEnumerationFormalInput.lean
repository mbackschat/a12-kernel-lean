import A12Kernel.Elaboration.AddressedEnumerationComputation
import A12Kernel.Elaboration.AddressedEnumerationFirstFilledComputation
import A12Kernel.Elaboration.ComputationFormalInput

/-! # Checked formal inputs for addressed Enumeration assignment -/

namespace A12Kernel

/-- Failure while composing selected formal-input preparation with addressed Enumeration assignment. -/
inductive AddressedEnumerationCheckedResultFault where
  | formalInput (cause : ComputationFormalInputPlanError)
  | preliminary (cause : CheckedIndexPreliminaryError)
  | execution (formalErrorsInOperands : List ComputationFormalInputFinding)
      (cause : AddressedEnumerationComputationFault)
  | assembly (formalErrorsInOperands : List ComputationFormalInputFinding)
      (cause : ComputationReportAssemblyFault)
  deriving Repr, DecidableEq

namespace CheckedAddressedEnumerationComputation

/-- Bind the literal-or-field source and computed Enumeration target to the shared eager inventory. -/
def formalInputPlan (operation : CheckedAddressedEnumerationComputation model) :
    Except ComputationFormalInputPlanError
      (CheckedComputationFormalInputPlan model) :=
  checkImplicitGuardFormalInputPlan model operation.source.fieldDependencies
    [operation.target.field]

/-- Prepare selected source findings and index state once, then execute through that exact view and check report assembly after successful execution, retaining findings beside faults. -/
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
  | .ok result =>
      (ComputationFormalInputFinding.assembleResult prepared.formalErrorsInOperands result)
        |>.mapError (.assembly prepared.formalErrorsInOperands)

end CheckedAddressedEnumerationComputation

/-- Failure while composing selected formal-input preparation with addressed Enumeration `FirstFilledValue`. -/
inductive AddressedEnumerationFirstFilledCheckedResultFault where
  | formalInput (cause : ComputationFormalInputPlanError)
  | preliminary (cause : CheckedIndexPreliminaryError)
  | execution (formalErrorsInOperands : List ComputationFormalInputFinding)
      (cause : AddressedEnumerationFirstFilledComputationFault)
  | assembly (formalErrorsInOperands : List ComputationFormalInputFinding)
      (cause : ComputationReportAssemblyFault)
  deriving Repr, DecidableEq

namespace CheckedAddressedEnumerationFirstFilledComputation

/-- Bind the complete ordered first-filled dependency inventory and computed Enumeration target to the shared eager inventory. -/
def formalInputPlan
    (operation : CheckedAddressedEnumerationFirstFilledComputation model) :
    Except ComputationFormalInputPlanError
      (CheckedComputationFormalInputPlan model) :=
  checkImplicitGuardFormalInputPlan model operation.source.fieldDependencies
    [operation.target.field]

/-- Prepare every selected operand once, then preserve lazy runtime reads while checking report assembly after successful execution. -/
def executeResultWithFormalInputs
    (operation : CheckedAddressedEnumerationFirstFilledComputation model)
    (input : CheckedDocument model) (world : Option World := none) :
    Except AddressedEnumerationFirstFilledCheckedResultFault
      (AddressedEnumerationFirstFilledComputationRunView model
        ComputationFormalInputFinding) := do
  let plan ← operation.formalInputPlan |>.mapError .formalInput
  let prepared ← plan.prepare input |>.mapError .preliminary
  match operation.executeResultWithRead (world := world) input
      prepared.preliminary.readComputation
      prepared.formalErrorsInOperands with
  | .error cause =>
      .error (.execution prepared.formalErrorsInOperands cause)
  | .ok result =>
      (ComputationFormalInputFinding.assembleResult prepared.formalErrorsInOperands result)
        |>.mapError (.assembly prepared.formalErrorsInOperands)

end CheckedAddressedEnumerationFirstFilledComputation

end A12Kernel
