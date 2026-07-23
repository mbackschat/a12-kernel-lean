import A12Kernel.Elaboration.CheckedIndexPreliminary

/-! # Checked index preliminary laws -/

namespace A12Kernel

@[simp] theorem indexPreliminary_mandatory_contract :
    IndexPreliminaryKind.mandatory.cause = .required ∧
      IndexPreliminaryKind.mandatory.verdict = .fired .omission ∧
      IndexPreliminaryKind.mandatory.errorCode = "mandatoryField" := by
  simp [IndexPreliminaryKind.cause, IndexPreliminaryKind.verdict,
    IndexPreliminaryKind.errorCode]

@[simp] theorem indexPreliminary_unique_contract :
    IndexPreliminaryKind.unique.cause = .duplicateIndex ∧
      IndexPreliminaryKind.unique.verdict = .fired .value ∧
      IndexPreliminaryKind.unique.errorCode = "uniqueIndex" := by
  simp [IndexPreliminaryKind.cause, IndexPreliminaryKind.verdict,
    IndexPreliminaryKind.errorCode]

/-- Preliminary findings alter only the addressed finding list; the base parsed payload remains available for duplicate-index content. -/
theorem checkedIndexPreliminary_preserves_parsed
    (preliminary : CheckedIndexPreliminary model) (address : CellAddr) :
    (preliminary.readAuthoredValidation address).map (·.parsed) =
      (preliminary.base.read address).map (·.parsed) := by
  unfold CheckedIndexPreliminary.readAuthoredValidation
  cases readResult : preliminary.base.read address with
  | error error => rfl
  | ok cell =>
      simp only [bind, Except.bind, Except.map]
      unfold CheckedIndexPreliminary.annotateCell
      cases preliminary.findingAt? address <;> rfl

end A12Kernel
