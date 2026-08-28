import A12Kernel.Elaboration.AddressedEnumerationFormalInput
import A12Kernel.Proofs.ComputationFormalInput

/-! # Addressed Enumeration formal-input laws -/

namespace A12Kernel

/-- Successful whole-call composition executes through the exact prepared read and projects its eager inventory unchanged into the String-shaped result. -/
theorem addressedEnumeration_executeResultWithFormalInputs_exact
    (operation : CheckedAddressedEnumerationComputation model)
    (input : CheckedDocument model)
    (plan : CheckedComputationFormalInputPlan model)
    (prepared : ComputationFormalInputPreparation model)
    (outcomes : List AddressedEnumerationComputationOutcome)
    (planned : operation.formalInputPlan = .ok plan)
    (preparation : plan.prepare input = .ok prepared)
    (executed : operation.executeWithRead input
      prepared.preliminary.readComputation = .ok outcomes) :
    (operation.executeResultWithFormalInputs input).map
      (fun view => view.string.formalErrorsInOperands) =
        .ok prepared.formalErrorsInOperands := by
  rw [CheckedAddressedEnumerationComputation.executeResultWithFormalInputs,
    planned]
  simp only [Except.mapError, bind, Except.bind, preparation]
  rw [CheckedAddressedEnumerationComputation.executeResultWithRead, executed]
  rfl

/-- A post-preparation addressed execution failure retains the exact eager inventory beside the unchanged existing fault. -/
theorem addressedEnumeration_executeResultWithFormalInputs_failure_exact
    (operation : CheckedAddressedEnumerationComputation model)
    (input : CheckedDocument model)
    (plan : CheckedComputationFormalInputPlan model)
    (prepared : ComputationFormalInputPreparation model)
    (fault : AddressedEnumerationComputationFault)
    (planned : operation.formalInputPlan = .ok plan)
    (preparation : plan.prepare input = .ok prepared)
    (executed : operation.executeResultWithRead input
      prepared.preliminary.readComputation
      prepared.formalErrorsInOperands = .error fault) :
    operation.executeResultWithFormalInputs input =
      .error (.execution prepared.formalErrorsInOperands fault) := by
  rw [CheckedAddressedEnumerationComputation.executeResultWithFormalInputs,
    planned]
  simp only [Except.mapError, bind, Except.bind, preparation, executed]

/-- Successful first-filled composition executes through the exact prepared read while retaining even eager findings for runtime-unreached operands. -/
theorem addressedEnumerationFirstFilled_executeResultWithFormalInputs_exact
    (operation : CheckedAddressedEnumerationFirstFilledComputation model)
    (input : CheckedDocument model)
    (plan : CheckedComputationFormalInputPlan model)
    (prepared : ComputationFormalInputPreparation model)
    (outcomes : List AddressedEnumerationComputationOutcome)
    (planned : operation.formalInputPlan = .ok plan)
    (preparation : plan.prepare input = .ok prepared)
    (executed : operation.executeWithRead input
      prepared.preliminary.readComputation = .ok outcomes) :
    (operation.executeResultWithFormalInputs input).map
      (fun view => view.string.formalErrorsInOperands) =
        .ok prepared.formalErrorsInOperands := by
  rw [CheckedAddressedEnumerationFirstFilledComputation.executeResultWithFormalInputs,
    planned]
  simp only [Except.mapError, bind, Except.bind, preparation]
  rw [CheckedAddressedEnumerationFirstFilledComputation.executeResultWithRead,
    executed]
  rfl

/-- A post-preparation first-filled execution failure retains the exact eager inventory beside the unchanged existing fault. -/
theorem addressedEnumerationFirstFilled_executeResultWithFormalInputs_failure_exact
    (operation : CheckedAddressedEnumerationFirstFilledComputation model)
    (input : CheckedDocument model)
    (plan : CheckedComputationFormalInputPlan model)
    (prepared : ComputationFormalInputPreparation model)
    (fault : AddressedEnumerationFirstFilledComputationFault)
    (planned : operation.formalInputPlan = .ok plan)
    (preparation : plan.prepare input = .ok prepared)
    (executed : operation.executeResultWithRead input
      prepared.preliminary.readComputation
      prepared.formalErrorsInOperands = .error fault) :
    operation.executeResultWithFormalInputs input =
      .error (.execution prepared.formalErrorsInOperands fault) := by
  rw [CheckedAddressedEnumerationFirstFilledComputation.executeResultWithFormalInputs,
    planned]
  simp only [Except.mapError, bind, Except.bind, preparation, executed]

end A12Kernel
