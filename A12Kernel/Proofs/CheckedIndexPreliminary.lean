import A12Kernel.Elaboration.CheckedIndexPreliminary

/-! # Checked full and partial generated-preliminary laws -/

namespace A12Kernel

private theorem Except.map_after_mapError
    (result : Except ε α) (mapError : ε → δ) (mapValue : α → β) :
    (result.mapError mapError).map mapValue =
      (result.map mapValue).mapError mapError := by
  cases result <;> rfl

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

private theorem checkedPartialPreliminary_annotation_preserves_parsed
    (view : CheckedPartialPreliminary model) (address : CellAddr)
    (relevant : view.isAddressRelevant address = true) :
    (view.readAuthoredValidation address).map (·.parsed) =
      (view.index.readAuthoredValidation address |>.mapError
        CheckedIndexPreliminaryError.document).map (·.parsed) := by
  unfold CheckedPartialPreliminary.readAuthoredValidation
  cases readResult : view.index.readAuthoredValidation address with
  | error error => rfl
  | ok cell =>
      simp only [Except.mapError, relevant, ↓reduceIte, Except.map]
      unfold CheckedPartialPreliminary.annotateRequiredCell
      cases verdictResult : view.requiredVerdictAt? address with
      | none => rfl
      | some verdict =>
          cases verdict with
          | notFired => rfl
          | unknown => rfl
          | fired polarity =>
              cases polarity <;> rfl

/-- The partial preliminary view changes only addressed findings. Neither relevance selection nor either generated channel can replace a parsed base payload. -/
theorem checkedPartialPreliminary_preserves_parsed
    (view : CheckedPartialPreliminary model) (address : CellAddr)
    (relevant : view.isAddressRelevant address = true) :
    (view.readAuthoredValidation address).map (·.parsed) =
      (view.index.base.read address |>.mapError
        CheckedIndexPreliminaryError.document).map (·.parsed) := by
  rw [checkedPartialPreliminary_annotation_preserves_parsed
    view address relevant]
  rw [Except.map_after_mapError, Except.map_after_mapError]
  exact congrArg
    (fun result =>
      result.mapError CheckedIndexPreliminaryError.document)
    (checkedIndexPreliminary_preserves_parsed view.index address)

end A12Kernel
