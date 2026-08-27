import A12Kernel.Elaboration.ComputationFormalInput

/-! # Checked direct-field computation formal-input laws -/

namespace A12Kernel

/-- Every collected finding belongs to a selected operand field and never to a computed target. -/
theorem computationFormalInputFinding_selected
    (plan : CheckedComputationFormalInputPlan model)
    (input : CheckedDocument model)
    (finding : ComputationFormalInputFinding)
    (member : finding ∈ plan.findings input) :
    plan.operandFields.contains finding.address.field = true ∧
      plan.computedFields.contains finding.address.field = false := by
  rw [CheckedComputationFormalInputPlan.findings,
    List.mem_flatMap] at member
  obtain ⟨placement, _, member⟩ := member
  by_cases included : plan.includesField placement.address.field = true
  · simp only [included, if_true, List.mem_map] at member
    obtain ⟨cause, _, equality⟩ := member
    subst finding
    simpa [CheckedComputationFormalInputPlan.includesField] using included
  · simp [included] at member

end A12Kernel
