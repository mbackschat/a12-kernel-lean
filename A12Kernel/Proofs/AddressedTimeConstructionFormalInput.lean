import A12Kernel.Elaboration.AddressedTimeConstructionFormalInput
import A12Kernel.Proofs.ComputationFormalInput

/-! # Addressed `Time(...)` formal-input laws -/

namespace A12Kernel

/-- Successful whole-call composition executes through the exact prepared read and projects its eager inventory unchanged into the Time result. -/
theorem addressedTimeConstruction_executeResultWithFormalInputs_exact
    (operation : CheckedAddressedTimeConstructionComputation model)
    (input : CheckedDocument model)
    (plan : CheckedComputationFormalInputPlan model)
    (prepared : ComputationFormalInputPreparation model)
    (outcomes : List AddressedTimeConstructionOutcome)
    (planned : operation.formalInputPlan = .ok plan)
    (preparation : plan.prepare input = .ok prepared)
    (executed : operation.executeWithRead input
      prepared.preliminary.readComputation = .ok outcomes) :
    (operation.executeResultWithFormalInputs input).map
      (fun view => view.time.formalErrorsInOperands) =
        .ok prepared.formalErrorsInOperands := by
  rw [CheckedAddressedTimeConstructionComputation.executeResultWithFormalInputs,
    planned]
  simp only [Except.mapError, bind, Except.bind, preparation]
  rw [CheckedAddressedTimeConstructionComputation.executeResultWithRead,
    executed]
  rfl

/-- A post-preparation addressed execution failure retains the exact eager inventory beside the unchanged existing fault. -/
theorem addressedTimeConstruction_executeResultWithFormalInputs_failure_exact
    (operation : CheckedAddressedTimeConstructionComputation model)
    (input : CheckedDocument model)
    (plan : CheckedComputationFormalInputPlan model)
    (prepared : ComputationFormalInputPreparation model)
    (fault : AddressedTimeConstructionFault)
    (planned : operation.formalInputPlan = .ok plan)
    (preparation : plan.prepare input = .ok prepared)
    (executed : operation.executeResultWithRead input
      prepared.preliminary.readComputation
      prepared.formalErrorsInOperands = .error fault) :
    operation.executeResultWithFormalInputs input =
      .error (.execution prepared.formalErrorsInOperands fault) := by
  rw [CheckedAddressedTimeConstructionComputation.executeResultWithFormalInputs,
    planned]
  simp only [Except.mapError, bind, Except.bind, preparation, executed]
  rfl

end A12Kernel
