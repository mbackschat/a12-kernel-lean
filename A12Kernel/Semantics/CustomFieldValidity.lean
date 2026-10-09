import A12Kernel.Semantics.CustomFieldType

/-! # A12Kernel.Semantics.CustomFieldValidity — explicit validity predicates over a partial registry

This capsule models the two-argument `Valid(field, "Name")` / `Invalid(field, "Name")` forms after String observation and validator-name resolution. Unlike a declared custom field, this consumer has no declaration-owned length bounds; it supplies the kernel's fixed German, stored-value context through the same validator interface.

The predefined types are a host client SPI, so the registry is **partial by construction** and the authored name may resolve to nothing. The model check does not consult it, so an unregistered name is legal. On a filled value, lookup failure aborts the enclosing rule and becomes a VALUE message for either polarity; it is not a true leaf inside a Boolean expression (Having runtime calibration, 2026-10-09). `evalValidation` preserves that effect, while `eval` projects the standalone rule observable.
-/

namespace A12Kernel

/-- Named-type validity consumes the checked String text or stored Enumeration token. Ingestion
already normalizes String line breaks once; repeating it changes CR-CRLF (spec/06 A, A.3). -/
def CellObservation.asTypeValidityText (observation : CellObservation) : CellObservation String :=
  match observation with
  | .value (.enum token) => .value token
  | other => other.asText

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

/-- Admit any nonempty authored name and retain whatever the host registry resolves for it. An unregistered name is legal, so its runtime lookup failure remains reachable rather than becoming a static rejection. -/
def elaborateCustomFieldValidity (world : World) (name : String) :
    Except CustomFieldValidityElabError CheckedCustomFieldValidity :=
  if name.isEmpty then
    .error .emptyTypeName
  else
    .ok { name, validator? := world.resolveCustomFieldValidator? name }

inductive CustomFieldValidityComputationResult where
  | notTrue
  | holds
  | poison (cause : FormalCause)
  | validatorUnavailable
  deriving Repr, DecidableEq

inductive CustomFieldValidityRuntimeFault where
  | validatorUnavailable
  deriving Repr, DecidableEq

namespace CheckedCustomFieldValidity

/-- Project the standalone rule result for one checked explicit validity predicate.

    The value-specified gate runs first and is registration-blind: empty and unavailable observations remain UNKNOWN whether or not a validator exists. A present nonempty value with a resolved validator is accepted exactly when that validator returns no rejection. Without a usable validator, both standalone rules produce VALUE. Composing callers must use `evalValidation` so that the enclosing rule catches the failure after Boolean evaluation aborts. -/
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

/-- Preserve missing-validator failure until the enclosing rule handler; the standalone `eval`
projection cannot be used inside Boolean expressions (Having runtime calibration, 2026-10-09). -/
def evalValidation (checked : CheckedCustomFieldValidity) (operation : CustomFieldValidityOp)
    (observation : CellObservation String) : Except CustomFieldValidityRuntimeFault Verdict :=
  match observation, checked.validator? with
  | .value value, none =>
      if value.isEmpty then .ok .unknown else .error .validatorUnavailable
  | _, _ => .ok (checked.eval operation observation)

/-- Computation additionally preserves reached source invalidity; both phases retain
missing-validator failure (computation probe, 2026-10-04; Having calibration, 2026-10-09). -/
def evalComputation (checked : CheckedCustomFieldValidity) (operation : CustomFieldValidityOp) :
    CellObservation String → CustomFieldValidityComputationResult
  | .empty => .notTrue
  | .unknown cause | .poison cause => .poison cause
  | .value value =>
      if value.isEmpty then .notTrue
      else match checked.validator? with
        | none => .validatorUnavailable
        | some _ => match checked.eval operation (.value value) with
            | .fired _ => .holds
            | _ => .notTrue

end CheckedCustomFieldValidity

end A12Kernel
