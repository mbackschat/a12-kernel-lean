import A12Kernel.Elaboration.AddressedDateRangeBoundPartFormalInput
import A12Kernel.Proofs.ComputationFormalInput

/-! # Addressed DateRange endpoint-component formal-input laws -/

namespace A12Kernel

/-- Successful whole-call composition preserves the prepared eager inventory beside the exact typed Number result. -/
theorem addressedDateRangeBoundPart_executeResultWithFormalInputs_exact
    (operation : CheckedAddressedDateRangeBoundPart model)
    (input : CheckedDocument model)
    (plan : CheckedComputationFormalInputPlan model)
    (prepared : ComputationFormalInputPreparation model)
    (numeric : NumericComputationRunView
      (ComputationFormalMessage Unit) CellAddr)
    (planned : operation.formalInputPlan = .ok plan)
    (preparation : plan.prepare input = .ok prepared)
    (executed : operation.executeResultWithRead input
      prepared.preliminary.readComputation (fun _ => ()) [] = .ok numeric) :
    (operation.executeResultWithFormalInputs input).map (fun view =>
      (view.formalErrorsInOperands, view.numeric)) =
        .ok (prepared.formalErrorsInOperands, numeric) := by
  rw [CheckedAddressedDateRangeBoundPart.executeResultWithFormalInputs,
    planned]
  simp only [Except.mapError, bind, Except.bind, preparation]
  rw [executed]
  rfl

/-- A post-preparation addressed failure retains the exact eager inventory beside the unchanged fault. -/
theorem addressedDateRangeBoundPart_executeResultWithFormalInputs_failure_exact
    (operation : CheckedAddressedDateRangeBoundPart model)
    (input : CheckedDocument model)
    (plan : CheckedComputationFormalInputPlan model)
    (prepared : ComputationFormalInputPreparation model)
    (fault : AddressedDateRangeBoundPartFault)
    (planned : operation.formalInputPlan = .ok plan)
    (preparation : plan.prepare input = .ok prepared)
    (executed : operation.executeResultWithRead input
      prepared.preliminary.readComputation (fun _ => ()) [] = .error fault) :
    operation.executeResultWithFormalInputs input =
      .error (.execution prepared.formalErrorsInOperands fault) := by
  rw [CheckedAddressedDateRangeBoundPart.executeResultWithFormalInputs,
    planned]
  simp only [Except.mapError, bind, Except.bind, preparation, executed]

end A12Kernel
