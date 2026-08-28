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

/-- Every selected generated preliminary finding obeys the same noncomputed operand boundary as cached input findings. -/
theorem computationFormalInputPreliminaryFinding_selected
    (plan : CheckedComputationFormalInputPlan model)
    (preliminary : CheckedIndexPreliminary model)
    (finding : ComputationFormalInputFinding)
    (member : finding ∈ plan.preliminaryFindings preliminary) :
    plan.operandFields.contains finding.address.field = true ∧
      plan.computedFields.contains finding.address.field = false := by
  rw [CheckedComputationFormalInputPlan.preliminaryFindings,
    List.mem_filterMap] at member
  obtain ⟨generated, _, member⟩ := member
  by_cases included : plan.includesField generated.address.field = true
  · simp only [included, if_true, Option.some.injEq] at member
    subst finding
    simpa [CheckedComputationFormalInputPlan.includesField] using included
  · simp [included] at member

/-- Cached and generated findings in the combined preparation inventory share one selected noncomputed field invariant. -/
theorem computationFormalInputFindingIncludingPreliminary_selected
    (plan : CheckedComputationFormalInputPlan model)
    (preliminary : CheckedIndexPreliminary model)
    (finding : ComputationFormalInputFinding)
    (member : finding ∈ plan.findingsIncludingPreliminary preliminary) :
    plan.operandFields.contains finding.address.field = true ∧
      plan.computedFields.contains finding.address.field = false := by
  rw [CheckedComputationFormalInputPlan.findingsIncludingPreliminary,
    List.mem_append] at member
  cases member with
  | inl cached =>
      exact computationFormalInputFinding_selected plan preliminary.base
        finding cached
  | inr generated =>
      exact computationFormalInputPreliminaryFinding_selected plan preliminary
        finding generated

end A12Kernel
