import A12Kernel.Semantics.CustomFieldValidity

/-! # A12Kernel.Proofs.CustomFieldValidity — explicit registered validity laws -/

namespace A12Kernel

theorem explicitCustomFieldValidationContext_exact :
    explicitCustomFieldValidationContext = {
      locale := "de_DE"
      minLength := none
      maxLength := none
      isDisplayValue := false
    } := by
  rfl

theorem elaborateCustomFieldValidity_missing (world : World) (name : String)
    (missing : world.resolveCustomFieldValidator? name = none) :
    elaborateCustomFieldValidity world name =
      .error (.missingValidator name) := by
  simp [elaborateCustomFieldValidity, requireCustomFieldValidator, missing] <;> rfl

theorem elaborateCustomFieldValidity_resolved (world : World) (name : String)
    (validator : RegisteredCustomFieldValidator)
    (resolved : world.resolveCustomFieldValidator? name = some validator) :
    elaborateCustomFieldValidity world name = .ok { name, validator } := by
  simp [elaborateCustomFieldValidity, requireCustomFieldValidator, resolved] <;> rfl

@[simp]
theorem customFieldValidity_empty_unknown
    (checked : CheckedCustomFieldValidity) (operation : CustomFieldValidityOp) :
    checked.eval operation .empty = .unknown := by
  cases operation <;> rfl

@[simp]
theorem customFieldValidity_unavailable_unknown
    (checked : CheckedCustomFieldValidity) (operation : CustomFieldValidityOp)
    (cause : FormalCause) :
    checked.eval operation (.unknown cause) = .unknown := by
  cases operation <;> rfl

/-- On a present nonempty value, `Valid` and `Invalid` are exact complements at full verdict granularity. -/
theorem customFieldValidity_present_complement
    (checked : CheckedCustomFieldValidity) (value : String)
    (nonempty : value.isEmpty = false) :
    (checked.eval .valid (.value value) = .fired .value ↔
      checked.eval .invalid (.value value) = .notFired) ∧
    (checked.eval .invalid (.value value) = .fired .value ↔
      checked.eval .valid (.value value) = .notFired) := by
  cases result : checked.validator value explicitCustomFieldValidationContext <;>
    simp [CheckedCustomFieldValidity.eval, nonempty, result]

/-- A registered rejection is used only as the predicate's accept/reject bit; explicit `Invalid` fires VALUE and does not expose or rewrite the project payload. -/
theorem customFieldValidity_rejection_fires_invalid
    (checked : CheckedCustomFieldValidity) (value : String)
    (rejection : RegisteredCustomRejection)
    (nonempty : value.isEmpty = false)
    (rejected : checked.validator value explicitCustomFieldValidationContext =
      some rejection) :
    checked.eval .invalid (.value value) = .fired .value := by
  simp [CheckedCustomFieldValidity.eval, nonempty, rejected]

end A12Kernel
