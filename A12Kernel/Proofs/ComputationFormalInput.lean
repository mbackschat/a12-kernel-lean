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
  · simp only [included, ite_true, List.mem_map] at member
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
  · simp only [included, ite_true, Option.some.injEq] at member
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

/-- A successful composition returns the run's exact result over the prepared read and findings. -/
theorem runWithFormalInputs_exact {Cause Result : Type}
    (input : CheckedDocument model) (plan : CheckedComputationFormalInputPlan model)
    (prepared : ComputationFormalInputPreparation model) (result : Result)
    (run : (CellAddr → Except CheckedDocumentError CheckedCell) →
      List ComputationFormalInputFinding → Except Cause Result)
    (preparation : plan.prepare input = .ok prepared)
    (executed : run prepared.preliminary.readComputation prepared.formalErrorsInOperands = .ok result)
    (assembled : ComputationFormalInputFinding.checkAssembly prepared.formalErrorsInOperands = .ok ()) :
    runWithFormalInputs (.ok plan) input run = .ok result := by
  simp only [runWithFormalInputs, Except.mapError, bind, Except.bind, preparation, executed, assembled, pure, Except.pure]

/-- A run fault after preparation retains the exact eager findings beside the unchanged fault. -/
theorem runWithFormalInputs_failure_exact {Cause Result : Type}
    (input : CheckedDocument model) (plan : CheckedComputationFormalInputPlan model)
    (prepared : ComputationFormalInputPreparation model) (fault : Cause)
    (run : (CellAddr → Except CheckedDocumentError CheckedCell) →
      List ComputationFormalInputFinding → Except Cause Result)
    (preparation : plan.prepare input = .ok prepared)
    (executed : run prepared.preliminary.readComputation prepared.formalErrorsInOperands = .error fault) :
    runWithFormalInputs (.ok plan) input run = .error (.execution prepared.formalErrorsInOperands fault) := by
  simp only [runWithFormalInputs, Except.mapError, bind, Except.bind, preparation, executed]

/-- A pointer collision after successful execution keeps the eager findings and exposes no result. -/
theorem runWithFormalInputs_assembly_failure_exact {Cause Result : Type}
    (input : CheckedDocument model) (plan : CheckedComputationFormalInputPlan model)
    (prepared : ComputationFormalInputPreparation model) (result : Result)
    (fault : ComputationReportAssemblyFault)
    (run : (CellAddr → Except CheckedDocumentError CheckedCell) →
      List ComputationFormalInputFinding → Except Cause Result)
    (preparation : plan.prepare input = .ok prepared)
    (executed : run prepared.preliminary.readComputation prepared.formalErrorsInOperands = .ok result)
    (collided : ComputationFormalInputFinding.checkAssembly prepared.formalErrorsInOperands = .error fault) :
    runWithFormalInputs (.ok plan) input run =
      .error (.assembly prepared.formalErrorsInOperands fault) := by
  simp only [runWithFormalInputs, Except.mapError, bind, Except.bind, preparation,
    executed, collided]

end A12Kernel
