import A12Kernel.Elaboration.AddressedDateRangeFirstFilledFormalInput
import A12Kernel.Proofs.ComputationFormalInput

/-! # Addressed DateRange `FirstFilledValue` formal-input laws -/

namespace A12Kernel

/-- Successful whole-call composition scans through the selected prepared read and projects its eager inventory unchanged into the DateRange result. -/
theorem addressedDateRangeFirstFilled_executeResultWithFormalInputs_exact
    (operation : CheckedAddressedDateRangeFirstFilledComputation model)
    (input : CheckedDocument model)
    (plan : CheckedComputationFormalInputPlan model)
    (prepared : ComputationFormalInputPreparation model)
    (outcomes : List AddressedDateRangeFirstFilledComputationOutcome)
    (planned : operation.formalInputPlan = .ok plan)
    (preparation : plan.prepare input = .ok prepared)
    (executed : operation.executeWithRead input
      prepared.preliminary.readComputation = .ok outcomes) :
    (operation.executeResultWithFormalInputs input).map
      (fun view => view.dateRange.formalErrorsInOperands) =
        .ok prepared.formalErrorsInOperands := by
  rw [CheckedAddressedDateRangeFirstFilledComputation.executeResultWithFormalInputs,
    planned]
  simp only [Except.mapError, bind, Except.bind, preparation]
  rw [CheckedAddressedDateRangeFirstFilledComputation.executeResultWithRead,
    executed]
  rfl

/-- A post-preparation addressed execution failure retains the exact eager inventory beside the unchanged existing fault. -/
theorem addressedDateRangeFirstFilled_executeResultWithFormalInputs_failure_exact
    (operation : CheckedAddressedDateRangeFirstFilledComputation model)
    (input : CheckedDocument model)
    (plan : CheckedComputationFormalInputPlan model)
    (prepared : ComputationFormalInputPreparation model)
    (fault : AddressedDateRangeFirstFilledComputationFault)
    (planned : operation.formalInputPlan = .ok plan)
    (preparation : plan.prepare input = .ok prepared)
    (executed : operation.executeResultWithRead input
      prepared.preliminary.readComputation
      prepared.formalErrorsInOperands = .error fault) :
    operation.executeResultWithFormalInputs input =
      .error (.execution prepared.formalErrorsInOperands fault) := by
  rw [CheckedAddressedDateRangeFirstFilledComputation.executeResultWithFormalInputs,
    planned]
  simp only [Except.mapError, bind, Except.bind, preparation, executed]
  rfl

end A12Kernel
