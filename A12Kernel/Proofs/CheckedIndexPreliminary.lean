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

/-- Away from an injected default, preliminary findings alter only the addressed finding list; the base parsed payload remains available for duplicate-index content. -/
theorem checkedIndexPreliminary_preserves_parsed
    (preliminary : CheckedIndexPreliminary model) (address : CellAddr)
    (notDefaulted : preliminary.defaultStoredAt? address = none) :
    (preliminary.readAuthoredValidation address).map (·.parsed) =
      (preliminary.base.read address).map (·.parsed) := by
  unfold CheckedIndexPreliminary.readAuthoredValidation
  cases readResult : preliminary.base.read address with
  | error error => rfl
  | ok cell =>
      simp only [bind, Except.bind, Except.map]
      unfold CheckedIndexPreliminary.stagedCell
      have noDefault :
          preliminary.defaulted.find? (fun defaulted =>
            defaulted.address == address) = none := by
        simpa [CheckedIndexPreliminary.defaultStoredAt?] using notDefaulted
      rw [noDefault]
      unfold CheckedIndexPreliminary.annotateCell
      cases preliminary.findingAt? address <;> rfl

/-- A selected injected default reads as its exact stored Enumeration token when no independent finding shadows it. -/
theorem checkedIndexPreliminary_default_read
    (preliminary : CheckedIndexPreliminary model) (address : CellAddr)
    (defaulted : CheckedIndexDefault) (base : CheckedCell)
    (selected : preliminary.defaulted.find? (fun candidate =>
      candidate.address == address) = some defaulted)
    (baseRead : preliminary.base.read address = .ok base)
    (noFinding : preliminary.findingAt? address = none) :
    preliminary.readAuthoredValidation address =
      .ok (checkAdmittedRawCell (.parsed (.enum defaulted.stored))) := by
  unfold CheckedIndexPreliminary.readAuthoredValidation
  rw [baseRead]
  simp only [bind, Except.bind]
  unfold CheckedIndexPreliminary.stagedCell
  rw [selected]
  unfold CheckedIndexPreliminary.annotateCell
  rw [noFinding]
  rfl

private theorem checkedPartialPreliminary_annotation_preserves_parsed
    (view : CheckedPartialPreliminary model) (address : CellAddr)
    (relevant : view.isAddressRelevant address = true)
    (available : view.silentlyUnavailable.contains address = false) :
    (view.readAuthoredValidation address).map
        (fun read => match read with
          | .checked cell => cell.parsed
          | .silentlyUnavailable => none) =
      (view.index.readAuthoredValidation address |>.mapError
        CheckedIndexPreliminaryError.document).map (·.parsed) := by
  unfold CheckedPartialPreliminary.readAuthoredValidation
  simp only [relevant, available]
  cases readResult : view.index.readAuthoredValidation address with
  | error error => rfl
  | ok cell =>
      simp only [Except.mapError, Except.map]
      unfold CheckedPartialPreliminary.annotateRequiredCell
      cases verdictResult : view.requiredVerdictAt? address with
      | none => rfl
      | some verdict =>
          cases verdict with
          | notFired => rfl
          | unknown => rfl
          | fired polarity =>
              cases polarity <;> rfl

/-- At an available relevant address, the partial preliminary view changes only addressed findings. Relevance selection and both generated channels preserve the parsed base payload. -/
theorem checkedPartialPreliminary_preserves_parsed
    (view : CheckedPartialPreliminary model) (address : CellAddr)
    (relevant : view.isAddressRelevant address = true)
    (available : view.silentlyUnavailable.contains address = false)
    (notDefaulted : view.index.defaultStoredAt? address = none) :
    (view.readAuthoredValidation address).map
        (fun read => match read with
          | .checked cell => cell.parsed
          | .silentlyUnavailable => none) =
      (view.index.base.read address |>.mapError
        CheckedIndexPreliminaryError.document).map (·.parsed) := by
  rw [checkedPartialPreliminary_annotation_preserves_parsed
    view address relevant available]
  rw [Except.map_after_mapError, Except.map_after_mapError]
  exact congrArg
    (fun result =>
      result.mapError CheckedIndexPreliminaryError.document)
    (checkedIndexPreliminary_preserves_parsed view.index address notDefaulted)

/-- Silent default suppression is a distinct call-local read outcome, not a fabricated formal cause. -/
theorem checkedPartialPreliminary_silent_read
    (view : CheckedPartialPreliminary model) (address : CellAddr)
    (relevant : view.isAddressRelevant address = true)
    (silent : view.silentlyUnavailable.contains address = true) :
    view.readAuthoredValidation address = .ok .silentlyUnavailable := by
  have member : address ∈ view.silentlyUnavailable := by
    simpa using silent
  simp [CheckedPartialPreliminary.readAuthoredValidation, relevant, member]
  rfl

/-- Every cause-free unavailable address belongs to the normalized partial relevance set; excluded defaults cannot leak into group state through this channel. -/
theorem checkedPartialPreliminary_silent_is_relevant
    (view : CheckedPartialPreliminary model) (address : CellAddr)
    (silent : address ∈ view.silentlyUnavailable) :
    view.isAddressRelevant address = true :=
  view.silentRelevant address silent

end A12Kernel
