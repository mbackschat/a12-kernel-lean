import A12Kernel.Elaboration.GeneratedComputationValidation

namespace A12Kernel

/-- Both scalar readers ignore field contents for a resolved fixed coordinate. Model ownership and
    absence of repeatable ancestry remain obligations of checked elaboration, not this raw law. -/
theorem fixedCurrentRepetition_scalar_readers
    (reference : ResolvedGroupReference)
    (validation : ValidationEvaluationContext)
    (computation : ScalarComputationContext) :
    validation.resolveNumericValidationAtom (.fixedCurrentRepetition reference) =
      .ok (.value 1 .fixed) ∧
    computation.readNumericComputationAtom (.fixedCurrentRepetition reference) =
      .ok (.value 1) := by
  exact ⟨rfl, rfl⟩

/-- Generated validation keeps the structural operand rather than rebuilding a literal, so the
    existing expression-preservation bridge retains its group identity through the arm crossing. -/
theorem fixedCurrentRepetition_generated_identity
    (model : FlatModel) (reference : ResolvedGroupReference) :
    (CheckedNumericComputationAtom.numeric (model := model)
      (.fixedCurrentRepetition reference)).toValidationAtom =
        .ok (.ordinary (.fixedCurrentRepetition reference)) := by
  rfl

end A12Kernel
