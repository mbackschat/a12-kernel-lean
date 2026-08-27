import A12Kernel.Elaboration.AddressedDateFromDateTimeFormalInput
import A12Kernel.Proofs.ComputationFormalInput

/-! # Addressed `DateFromDateTime` formal-input laws -/

namespace A12Kernel

/-- The composed FullDate result's formal-input channel is exactly the eager checked-plan inventory. -/
theorem addressedDateFromDateTime_executeResultWithFormalInputs_exact
    (operation : CheckedAddressedDateFromDateTime model)
    (input : CheckedDocument model)
    (plan : CheckedComputationFormalInputPlan model)
    (outcomes : List AddressedDateFromDateTimeOutcome)
    (view : AddressedDateFromDateTimeRunView model
      ComputationFormalInputFinding)
    (planned : operation.formalInputPlan = .ok plan)
    (executed : operation.execute input = .ok outcomes)
    (produced : operation.executeResultWithFormalInputs input = .ok view) :
    view.fullDate.formalErrorsInOperands = plan.findings input := by
  rw [CheckedAddressedDateFromDateTime.executeResultWithFormalInputs,
    planned] at produced
  simp only [bind, Except.bind, Except.mapError] at produced
  rw [CheckedAddressedDateFromDateTime.executeResult, executed] at produced
  simp only [bind, Except.bind, pure, Except.pure,
    Except.ok.injEq] at produced
  subst view
  rfl

end A12Kernel
