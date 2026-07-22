import A12Kernel.Semantics.CustomFieldType

/-! # A12Kernel.Semantics.CustomFieldValidity — explicit registered validity predicates

This capsule models the two-argument `Valid(field, "Name")` / `Invalid(field, "Name")` forms after String observation and exact validator-name resolution. Unlike a declared custom field, this consumer has no declaration-owned length bounds; it supplies the kernel's fixed German, stored-value context through the same validator interface.
-/

namespace A12Kernel

inductive CustomFieldValidityOp where
  | valid
  | invalid
  deriving Repr, DecidableEq

/-- A checked explicit predicate owns the exact validator resolved for its authored name. -/
structure CheckedCustomFieldValidity where
  name : String
  validator : RegisteredCustomFieldValidator

/-- The explicit predicate's context has no declaration from which either bound could arise. -/
def explicitCustomFieldValidationContext : CustomFieldValidationContext where
  locale := "de_DE"
  minLength := none
  maxLength := none
  isDisplayValue := false

/-- Reject an unregistered authored name during checked construction. -/
def elaborateCustomFieldValidity (world : World) (name : String) :
    Except CustomFieldTypeElabError CheckedCustomFieldValidity := do
  let validator ← requireCustomFieldValidator world name
  pure { name, validator }

namespace CheckedCustomFieldValidity

/-- Evaluate one checked explicit validity predicate. Empty and unavailable observations remain UNKNOWN; a present nonempty value is accepted exactly when the registered validator returns no rejection. -/
def eval (checked : CheckedCustomFieldValidity)
    (operation : CustomFieldValidityOp)
    (observation : CellObservation String) : Verdict :=
  match observation with
  | .empty => .unknown
  | .unknown _ => .unknown
  | .poison _ => .unknown
  | .value value =>
      if value.isEmpty then
        .unknown
      else
        match operation, checked.validator value explicitCustomFieldValidationContext with
        | .valid, none => .fired .value
        | .valid, some _ => .notFired
        | .invalid, none => .notFired
        | .invalid, some _ => .fired .value

end CheckedCustomFieldValidity

end A12Kernel
