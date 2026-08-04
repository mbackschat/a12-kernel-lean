import A12Kernel.Semantics.CustomFieldType

/-! # A12Kernel.Semantics.CustomFieldValidity — explicit validity predicates over a partial registry

This capsule models the two-argument `Valid(field, "Name")` / `Invalid(field, "Name")` forms after String observation and validator-name resolution. Unlike a declared custom field, this consumer has no declaration-owned length bounds; it supplies the kernel's fixed German, stored-value context through the same validator interface.

The predefined types are a host client SPI, so the registry is **partial by construction** and the authored name may resolve to nothing. The model check does not consult it, which makes an unregistered name legal and its runtime behaviour degenerate rather than rejected: on a filled value both polarities fire, so they are complements only where a validator exists. That observable is measured across both kernel strategies; its cause is unresolved on both sides and is deliberately not modelled here. [`SG7`](../../docs/SEMANTICS-GAPS.md) owns the open mechanism and this capsule's residual static boundary.
-/

namespace A12Kernel

inductive CustomFieldValidityOp where
  | valid
  | invalid
  deriving Repr, DecidableEq

/-- Static rejection classes of the authored type name. Registry membership is deliberately absent, because the model check requires only a nonempty name. -/
inductive CustomFieldValidityElabError where
  | emptyTypeName
  deriving Repr, DecidableEq

/-- A checked explicit predicate owns the resolution outcome for its authored name.

    `validator? = none` covers both kernel states in which no usable validator exists — no factory supplied at all, and a factory present that returns nothing for the name. They are measured indistinguishable in every observed cell, so collapsing them is the accurate representation rather than a lost distinction. -/
structure CheckedCustomFieldValidity where
  name : String
  validator? : Option RegisteredCustomFieldValidator

/-- The explicit predicate's context has no declaration from which either bound could arise. -/
def explicitCustomFieldValidationContext : CustomFieldValidationContext where
  locale := "de_DE"
  minLength := none
  maxLength := none
  isDisplayValue := false

/-- Admit any nonempty authored name and retain whatever the host registry resolves for it. An unregistered name is legal, so its degenerate runtime behaviour is reached rather than replaced by a checked rejection. -/
def elaborateCustomFieldValidity (world : World) (name : String) :
    Except CustomFieldValidityElabError CheckedCustomFieldValidity :=
  if name.isEmpty then
    .error .emptyTypeName
  else
    .ok { name, validator? := world.resolveCustomFieldValidator? name }

namespace CheckedCustomFieldValidity

/-- Evaluate one checked explicit validity predicate.

    The value-specified gate runs first and is registration-blind: empty and unavailable observations remain UNKNOWN whether or not a validator exists. A present nonempty value with a resolved validator is accepted exactly when that validator returns no rejection. Without a usable validator the predicate is degenerate and **both** polarities fire VALUE on the same value, which is the measured observable and not an inferred failure mode. -/
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
        match checked.validator? with
        | none => .fired .value
        | some validator =>
            match operation, validator value explicitCustomFieldValidationContext with
            | .valid, none => .fired .value
            | .valid, some _ => .notFired
            | .invalid, none => .notFired
            | .invalid, some _ => .fired .value

end CheckedCustomFieldValidity

end A12Kernel
