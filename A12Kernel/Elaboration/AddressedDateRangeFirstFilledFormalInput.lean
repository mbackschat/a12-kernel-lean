import A12Kernel.Elaboration.AddressedDateRangeFirstFilledComputation
import A12Kernel.Elaboration.ComputationFormalInput

/-! # Checked formal inputs for addressed DateRange `FirstFilledValue` -/

namespace A12Kernel

/-- Failure while composing the selected formal-input preliminary with an addressed sibling-star DateRange scan. -/
inductive AddressedDateRangeFirstFilledCheckedResultFault where
  | formalInput (cause : ComputationFormalInputPlanError)
  | preliminary (cause : CheckedIndexPreliminaryError)
  | execution (formalErrorsInOperands : List ComputationFormalInputFinding)
      (cause : AddressedDateRangeFirstFilledComputationFault)
  deriving Repr, DecidableEq

namespace CheckedAddressedDateRangeFirstFilledComputation

/-- The single DateRange source declaration used for scheduling and eager formal-input collection. -/
def fieldDependencies
    (operation : CheckedAddressedDateRangeFirstFilledComputation model) :
    List FieldId :=
  [operation.source.declaration.id]

/-- Bind the sibling-star source and computed DateRange target to the shared eager inventory. -/
def formalInputPlan
    (operation : CheckedAddressedDateRangeFirstFilledComputation model) :
    Except ComputationFormalInputPlanError
      (CheckedComputationFormalInputPlan model) :=
  checkComputationFormalInputPlan model operation.fieldDependencies
    [operation.targetField]

/-- Prepare the selected exact source view once, then scan and project the addressed DateRange result while retaining the eager inventory on later faults. -/
def executeResultWithFormalInputs
    (operation : CheckedAddressedDateRangeFirstFilledComputation model)
    (input : CheckedDocument model) :
    Except AddressedDateRangeFirstFilledCheckedResultFault
      (AddressedDateRangeFirstFilledComputationRunView model
        ComputationFormalInputFinding) := do
  let plan ← operation.formalInputPlan |>.mapError .formalInput
  let prepared ← plan.prepare input |>.mapError .preliminary
  match operation.executeResultWithRead input
      prepared.preliminary.readComputation
      prepared.formalErrorsInOperands with
  | .ok view => pure view
  | .error cause => throw (.execution prepared.formalErrorsInOperands cause)

end CheckedAddressedDateRangeFirstFilledComputation

end A12Kernel
