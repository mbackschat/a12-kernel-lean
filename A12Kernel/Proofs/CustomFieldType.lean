import A12Kernel.Semantics.CustomFieldType

/-! # A12Kernel.Proofs.CustomFieldType — registered validator observation laws -/

namespace A12Kernel

theorem customFieldValidationContext_defaults (name locale : String) :
    ({ name } : CustomFieldTypeDeclaration).validationContext locale = {
      locale
      minLength := some 1
      maxLength := some 999
      isDisplayValue := false
    } := by
  rfl

theorem elaborateCustomFieldType_missing (world : World)
    (declaration : CustomFieldTypeDeclaration)
    (missing : world.resolveCustomFieldValidator? declaration.name = none) :
    elaborateCustomFieldType world declaration =
      .error (.missingValidator declaration.name) := by
  simp [elaborateCustomFieldType, requireCustomFieldValidator, missing] <;> rfl

theorem elaborateCustomFieldType_resolved (world : World)
    (declaration : CustomFieldTypeDeclaration)
    (validator : RegisteredCustomFieldValidator)
    (resolved : world.resolveCustomFieldValidator? declaration.name = some validator) :
    elaborateCustomFieldType world declaration =
      .ok { declaration, validator } := by
  simp [elaborateCustomFieldType, requireCustomFieldValidator, resolved] <;> rfl

@[simp]
theorem customFieldType_nonrelevant_is_unsampled
    (checked : CheckedCustomFieldType) (locale : String) (raw : RawCell String) :
    checked.checkRelevantRaw locale false raw = none := by
  rfl

@[simp]
theorem customFieldType_empty_bypasses_validator
    (checked : CheckedCustomFieldType) (locale : String) :
    checked.checkRelevantRaw locale true .empty = some {
      rawPresent := false
      parsed := none
      findings := []
    } := by
  rfl

@[simp]
theorem customFieldType_parsedEmpty_bypasses_validator
    (checked : CheckedCustomFieldType) (locale : String) :
    checked.checkRelevantRaw locale true (.parsed "") = some {
      rawPresent := true
      parsed := none
      findings := []
    } := by
  rfl

theorem customFieldType_rejection_exact (checked : CheckedCustomFieldType)
    (locale value : String) (rejection : RegisteredCustomRejection)
    (nonempty : value.isEmpty = false)
    (rejected : checked.validator value
      (checked.declaration.validationContext locale) = some rejection)
    (unavailable : rejection.admitsValue = false) :
    checked.checkRelevantRaw locale true (.parsed value) = some {
      rawPresent := true
      parsed := none
      findings := [.registeredCustomValidation rejection]
    } := by
  simp [CheckedCustomFieldType.checkRelevantRaw,
    CheckedCustomFieldType.checkStringRaw,
    CheckedCustomFieldType.classifyString, nonempty, rejected, unavailable]

theorem customFieldType_rejection_phase_projection
    (checked : CheckedCustomFieldType) (locale value : String)
    (rejection : RegisteredCustomRejection)
    (nonempty : value.isEmpty = false)
    (rejected : checked.validator value
      (checked.declaration.validationContext locale) = some rejection)
    (unavailable : rejection.admitsValue = false) :
    checked.checkRelevantRaw locale true (.parsed value) = some {
      rawPresent := true
      parsed := none
      findings := [.registeredCustomValidation rejection]
    } ∧
    observeCell .validation {
      rawPresent := true, parsed := (none : Option String)
      findings := [.registeredCustomValidation rejection]
    } = .unknown (.registeredCustomValidation rejection) ∧
    observeCell .computation {
      rawPresent := true, parsed := (none : Option String)
      findings := [.registeredCustomValidation rejection]
    } = .poison (.registeredCustomValidation rejection) := by
  exact ⟨customFieldType_rejection_exact checked locale value rejection nonempty rejected unavailable,
    rfl, rfl⟩

/-- A reserved callback result keeps its exact report beside the normalized, readable value. -/
theorem customFieldType_report_exact (checked : CheckedCustomFieldType)
    (locale value : String) (rejection : RegisteredCustomRejection)
    (nonempty : value.isEmpty = false)
    (reported : checked.validator value
      (checked.declaration.validationContext locale) = some rejection)
    (admitted : rejection.admitsValue = true) :
    checked.checkRelevantRaw locale true (.parsed value) = some {
      rawPresent := true
      parsed := some (normalizeEvaluatedString value)
      findings := []
      reports := [.registeredCustomValidation rejection]
    } := by
  simp [CheckedCustomFieldType.checkRelevantRaw, CheckedCustomFieldType.checkStringRaw,
    CheckedCustomFieldType.classifyString, nonempty, reported, admitted]

/-- Both phases read the admitted report's value; the report remains available to formal output. -/
theorem customFieldType_report_phase_projection (checked : CheckedCustomFieldType)
    (locale value : String) (rejection : RegisteredCustomRejection) (phase : Phase)
    (nonempty : value.isEmpty = false)
    (reported : checked.validator value
      (checked.declaration.validationContext locale) = some rejection)
    (admitted : rejection.admitsValue = true) :
    (checked.checkRelevantRaw locale true (.parsed value)).map
      (fun cell => (observeCell phase cell, cell.formalReports)) =
      some (.value (normalizeEvaluatedString value), [.registeredCustomValidation rejection]) := by
  rw [customFieldType_report_exact checked locale value rejection nonempty reported admitted]
  cases phase <;> rfl

/-- Exact spelling is necessary: a trailing-space near code still makes validation unavailable. -/
theorem customFieldType_report_requires_exactCode :
    (({
      declaration := { name := "NearCode" }
      validator := fun _ _ => some { projectCode := "testIDNummer " }
    } : CheckedCustomFieldType).checkRelevantRaw "en_US" true (.parsed "x")).map
      (observeCell .validation) =
      some (.unknown (.registeredCustomValidation { projectCode := "testIDNummer " })) := by
  decide

end A12Kernel
