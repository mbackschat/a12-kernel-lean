import A12Kernel.Elaboration.AddressedTimeConstructionFormalInput
import A12Kernel.Proofs.ComputationFormalInput

/-! # Addressed `Time(...)` formal-input laws -/

namespace A12Kernel

/-- The composed Time result's formal-input channel is exactly the eager checked-plan inventory. -/
theorem addressedTimeConstruction_executeResultWithFormalInputs_exact
    (operation : CheckedAddressedTimeConstructionComputation model)
    (input : CheckedDocument model)
    (plan : CheckedComputationFormalInputPlan model)
    (outcomes : List AddressedTimeConstructionOutcome)
    (view : AddressedTimeConstructionRunView model
      ComputationFormalInputFinding)
    (planned : operation.formalInputPlan = .ok plan)
    (executed : operation.execute input = .ok outcomes)
    (produced : operation.executeResultWithFormalInputs input = .ok view) :
    view.time.formalErrorsInOperands = plan.findings input := by
  rw [CheckedAddressedTimeConstructionComputation.executeResultWithFormalInputs,
    planned] at produced
  simp only [bind, Except.bind, Except.mapError] at produced
  rw [CheckedAddressedTimeConstructionComputation.executeResult,
    executed] at produced
  simp only [bind, Except.bind, pure, Except.pure,
    Except.ok.injEq] at produced
  subst view
  rfl

end A12Kernel
