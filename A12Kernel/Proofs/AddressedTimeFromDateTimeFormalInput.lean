import A12Kernel.Elaboration.AddressedTimeFromDateTimeFormalInput
import A12Kernel.Proofs.ComputationFormalInput

/-! # Addressed `TimeFromDateTime` formal-input laws -/

namespace A12Kernel

/-- Successful whole-call composition executes through the exact prepared read and projects its eager inventory unchanged into the Time result. -/
theorem addressedTimeFromDateTime_executeResultWithFormalInputs_exact
    (operation : CheckedAddressedTimeFromDateTime model)
    (input : CheckedDocument model)
    (plan : CheckedComputationFormalInputPlan model)
    (prepared : ComputationFormalInputPreparation model)
    (outcomes : List AddressedTimeFromDateTimeOutcome)
    (planned : operation.formalInputPlan = .ok plan)
    (preparation : plan.prepare input = .ok prepared)
    (executed : operation.executeWithRead input
      prepared.preliminary.readComputation = .ok outcomes)
    (assembled : ComputationFormalInputFinding.checkAssembly prepared.formalErrorsInOperands = .ok ()) :
    (operation.executeResultWithFormalInputs input).map
      (fun view => view.time.formalErrorsInOperands) =
        .ok prepared.formalErrorsInOperands := by
  rw [CheckedAddressedTimeFromDateTime.executeResultWithFormalInputs,
    planned]
  simp only [Except.mapError, bind, Except.bind, preparation]
  rw [CheckedAddressedTimeFromDateTime.executeResultWithRead, executed]
  simp [ComputationFormalInputFinding.assembleResult, assembled, bind, Except.bind, pure, Except.pure, Except.map] <;> rfl

/-- A post-preparation addressed execution failure retains the exact eager inventory beside the unchanged existing fault. -/
theorem addressedTimeFromDateTime_executeResultWithFormalInputs_failure_exact
    (operation : CheckedAddressedTimeFromDateTime model)
    (input : CheckedDocument model)
    (plan : CheckedComputationFormalInputPlan model)
    (prepared : ComputationFormalInputPreparation model)
    (fault : AddressedTimeFromDateTimeFault)
    (planned : operation.formalInputPlan = .ok plan)
    (preparation : plan.prepare input = .ok prepared)
    (executed : operation.executeResultWithRead input
      prepared.preliminary.readComputation
      prepared.formalErrorsInOperands = .error fault) :
    operation.executeResultWithFormalInputs input =
      .error (.execution prepared.formalErrorsInOperands fault) := by
  rw [CheckedAddressedTimeFromDateTime.executeResultWithFormalInputs,
    planned]
  simp only [Except.mapError, bind, Except.bind, preparation, executed]
  rfl

end A12Kernel
