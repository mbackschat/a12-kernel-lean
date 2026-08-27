import A12Kernel.Elaboration.AddressedEnumerationFormalInput
import A12Kernel.Proofs.ComputationFormalInput

/-! # Addressed Enumeration formal-input laws -/

namespace A12Kernel

/-- The composed String-shaped result's formal-input channel is exactly the eager checked-plan inventory. -/
theorem addressedEnumeration_executeResultWithFormalInputs_exact
    (operation : CheckedAddressedEnumerationComputation model)
    (input : CheckedDocument model)
    (plan : CheckedComputationFormalInputPlan model)
    (outcomes : List AddressedEnumerationComputationOutcome)
    (view : AddressedEnumerationComputationRunView model
      ComputationFormalInputFinding)
    (planned : operation.formalInputPlan = .ok plan)
    (executed : operation.execute input = .ok outcomes)
    (produced : operation.executeResultWithFormalInputs input = .ok view) :
    view.string.formalErrorsInOperands = plan.findings input := by
  rw [CheckedAddressedEnumerationComputation.executeResultWithFormalInputs,
    planned] at produced
  simp only [bind, Except.bind, Except.mapError] at produced
  rw [CheckedAddressedEnumerationComputation.executeResult,
    executed] at produced
  simp only [bind, Except.bind, pure, Except.pure,
    Except.ok.injEq] at produced
  subst view
  rfl

end A12Kernel
