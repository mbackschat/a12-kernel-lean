import A12Kernel.Semantics.CustomFieldValidity

/-! # A12Kernel.Proofs.CustomFieldValidity — explicit validity laws over a partial registry

Complementation is proved only where the authored name resolved, and the accompanying non-law shows that hypothesis is load-bearing. -/

namespace A12Kernel

theorem explicitCustomFieldValidationContext_exact :
    explicitCustomFieldValidationContext = {
      locale := "de_DE"
      minLength := none
      maxLength := none
      isDisplayValue := false
    } := by
  rfl

theorem elaborateCustomFieldValidity_emptyName (world : World) (name : String)
    (empty : name.isEmpty = true) :
    elaborateCustomFieldValidity world name = .error .emptyTypeName := by
  simp [elaborateCustomFieldValidity, empty]

/-- Checked construction is registry-blind beyond recording the outcome: every nonempty name is admitted and carries exactly what the world resolved, so the registered and unsupplied certificates are two rewrites of one law. -/
theorem elaborateCustomFieldValidity_admits (world : World) (name : String)
    (nonempty : name.isEmpty = false) :
    elaborateCustomFieldValidity world name =
      .ok { name, validator? := world.resolveCustomFieldValidator? name } := by
  simp [elaborateCustomFieldValidity, nonempty]

/-- The value-specified gate is registration-blind: it holds for every certificate, whether or not its name resolved. -/
@[simp]
theorem customFieldValidity_empty_unknown
    (checked : CheckedCustomFieldValidity) (operation : CustomFieldValidityOp) :
    checked.eval operation .empty = .unknown := by
  cases operation <;> rfl

/-- Present-empty is the same gate, and the second measured empty cell. -/
@[simp]
theorem customFieldValidity_valueEmpty_unknown
    (checked : CheckedCustomFieldValidity) (operation : CustomFieldValidityOp)
    (value : String) (empty : value.isEmpty = true) :
    checked.eval operation (.value value) = .unknown := by
  simp [CheckedCustomFieldValidity.eval, empty]

@[simp]
theorem customFieldValidity_unavailable_unknown
    (checked : CheckedCustomFieldValidity) (operation : CustomFieldValidityOp)
    (cause : FormalCause) :
    checked.eval operation (.unknown cause) = .unknown := by
  cases operation <;> rfl

/-- With no usable validator the predicate is degenerate: on one present nonempty value **both** polarities fire VALUE. This is the measured observable; its cause is unresolved and unmodelled. -/
theorem customFieldValidity_unsupplied_fires_both
    (checked : CheckedCustomFieldValidity) (value : String)
    (operation : CustomFieldValidityOp)
    (nonempty : value.isEmpty = false)
    (unsupplied : checked.validator? = none) :
    checked.eval operation (.value value) = .fired .value := by
  simp [CheckedCustomFieldValidity.eval, nonempty, unsupplied]

/-- Neither polarity ever types a firing as OMISSION, in either registration state. Filling the operand is not what would clear this predicate, so a consumer may treat every firing it produces as value-typed. -/
theorem customFieldValidity_never_omission
    (checked : CheckedCustomFieldValidity) (operation : CustomFieldValidityOp)
    (observation : CellObservation String) :
    checked.eval operation observation ≠ .fired .omission := by
  cases observation with
  | empty => simp
  | unknown cause => simp
  | poison cause => simp [CheckedCustomFieldValidity.eval]
  | value value =>
      cases empty : value.isEmpty with
      | true => simp [customFieldValidity_valueEmpty_unknown checked operation value empty]
      | false =>
          cases resolved : checked.validator? with
          | none =>
              simp [customFieldValidity_unsupplied_fires_both checked value operation
                empty resolved]
          | some validator =>
              cases result : validator value explicitCustomFieldValidationContext <;>
                cases operation <;>
                simp [CheckedCustomFieldValidity.eval, empty, resolved, result]

/-- On a present nonempty value **whose name resolved**, `Valid` and `Invalid` are exact complements at full verdict granularity. The hypothesis is not decoration: see `customFieldValidity_complement_needs_validator`. -/
theorem customFieldValidity_present_complement
    (checked : CheckedCustomFieldValidity) (value : String)
    (validator : RegisteredCustomFieldValidator)
    (nonempty : value.isEmpty = false)
    (resolved : checked.validator? = some validator) :
    (checked.eval .valid (.value value) = .fired .value ↔
      checked.eval .invalid (.value value) = .notFired) ∧
    (checked.eval .invalid (.value value) = .fired .value ↔
      checked.eval .valid (.value value) = .notFired) := by
  cases result : validator value explicitCustomFieldValidationContext <;>
    simp [CheckedCustomFieldValidity.eval, nonempty, resolved, result]

/-- The nearest false generalization of the complement law: dropping its resolved-validator hypothesis makes it false, because an unsupplied name fires both polarities. -/
theorem customFieldValidity_complement_needs_validator :
    ¬ ∀ (checked : CheckedCustomFieldValidity) (value : String),
        value.isEmpty = false →
        (checked.eval .valid (.value value) = .fired .value ↔
          checked.eval .invalid (.value value) = .notFired) := by
  intro law
  have fires := fun operation =>
    customFieldValidity_unsupplied_fires_both
      { name := "NoSuchType", validator? := none } "x" operation (by decide) rfl
  have collapsed := (law { name := "NoSuchType", validator? := none } "x" (by decide)).mp
    (fires .valid)
  rw [fires .invalid] at collapsed
  exact absurd collapsed (by decide)

/-- A registered rejection is used only as the predicate's accept/reject bit; explicit `Invalid` fires VALUE and does not expose or rewrite the project payload. -/
theorem customFieldValidity_rejection_fires_invalid
    (checked : CheckedCustomFieldValidity) (value : String)
    (validator : RegisteredCustomFieldValidator)
    (rejection : RegisteredCustomRejection)
    (nonempty : value.isEmpty = false)
    (resolved : checked.validator? = some validator)
    (rejected : validator value explicitCustomFieldValidationContext =
      some rejection) :
    checked.eval .invalid (.value value) = .fired .value := by
  simp [CheckedCustomFieldValidity.eval, nonempty, resolved, rejected]

end A12Kernel
