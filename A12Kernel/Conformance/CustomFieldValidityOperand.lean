import A12Kernel.Elaboration.CustomFieldValidity

/-! # A12Kernel.Conformance.CustomFieldValidityOperand — the value-validation operand slot

`Valid(field, "Name")` and `Invalid(field, "Name")` take a single unstarred field whose declared
type is String, Enumeration, or extensible Enumeration, and each refusal at that slot carries its
own Kernel class. The rows below are that admitted set with one refused member per measured kind,
so the claim reads as a boundary rather than as a list of things that happened to work.

**The Custom row is the one that cannot be inferred.** A field declared with a `CustomFieldType` is
the operand a reader expects the predicate to accept, and it is refused; in this project's flat
model it is a String declaration carrying `customType`, so an implementation gating on
`policy.kind` admits it silently. The plain-String control beside it is what makes that row about
the custom declaration rather than about String.

Static admission only. Nothing here invokes a validator or observes a verdict, and the group and
starred operands the Kernel also refuses are not expressible in this signature.
-/

namespace A12Kernel.Conformance.CustomFieldValidityOperand

open A12Kernel

private def unsigned : NumField := { scale := 0, signed := false }

/-- One declaration per candidate kind, plus the two String declarations the Custom row needs to be
    separated from: a plain evaluated String and one carrying a registered custom type. -/
private def probeModel : FlatModel :=
  { fields := [
      { id := 1, groupPath := ["Probe"], name := "Text",
        policy := { kind := .string } },
      { id := 2, groupPath := ["Probe"], name := "Choice",
        policy := { kind := .enumeration },
        enumeration := some { storedTokens := ["A", "B"] } },
      { id := 3, groupPath := ["Probe"], name := "Amount",
        policy := { kind := .number unsigned } },
      { id := 4, groupPath := ["Probe"], name := "Flag",
        policy := { kind := .boolean } },
      { id := 5, groupPath := ["Probe"], name := "Agreed",
        policy := { kind := .confirm } },
      { id := 6, groupPath := ["Probe"], name := "Iban",
        policy := { kind := .string },
        customType := some { name := "IBAN" } },
      { id := 7, groupPath := ["Probe"], name := "DueOn",
        policy := { kind := .temporal .date TemporalComponents.fullDate },
        temporalTargetPolicy := some { format := "dd.MM.yyyy" } },
      { id := 8, groupPath := ["Probe"], name := "Blob",
        policy := { kind := .string }, stringValueMode := .raw }]
    repeatableGroups := [] }

private def admission? (source : FieldId) : Option KernelStaticDiagnostic :=
  match elaborateCustomFieldValidityOperand probeModel source with
  | .ok _ => none
  | .error error => error.diagnostic?

private def admitted (source : FieldId) : Bool :=
  (elaborateCustomFieldValidityOperand probeModel source).toOption.isSome

/-! ## The admitted set -/

example : admitted 1 = true := by native_decide

example : admitted 2 = true := by native_decide

/-! ## The measured refusals, each naming the admitted set -/

example : admission? 3 = some .noStringOrEnumOrExtEnum := by native_decide

example : admission? 4 = some .noStringOrEnumOrExtEnum := by native_decide

example : admission? 5 = some .noStringOrEnumOrExtEnum := by native_decide

/- The Custom-typed declaration. Its kind is `.string`, so this row and the `Text` row above differ
   in nothing a kind-keyed gate can see. -/
example : admitted 6 = false := by native_decide

example : admission? 6 = some .noStringOrEnumOrExtEnum := by native_decide

/-! ## Refused with no class claimed

A temporal operand lies outside the admitted set the Kernel's own text names, so it is refused —
but no row observed *which* class it draws, and this vocabulary reports `none` for an unestablished
mapping rather than the plausible neighbouring code. -/

example : admitted 7 = false := by native_decide

example : admission? 7 = none := by native_decide

/- A **raw** String is refused by this theory rather than by an observed Kernel gate: it exposes no
   evaluation value, so no observation could reach a validator. It is also the nearest
   representable candidate for the *value-validation* qualifier the canonical clause puts on this
   operand, which no authored declaration was able to separate — recorded as a candidate, claimed
   as nothing. The evaluated String at id 1 is the control that keeps this row about the value
   mode. -/
example : admitted 8 = false := by native_decide

example : admission? 8 = none := by native_decide

/-! ## The leaf reads its operand's **checked** cell, not the stored text

Admission alone leaves the predicate unusable: `CustomFieldValidity.eval` consumes a
`CellObservation String` that a caller had to build by hand. Pairing the admitted operand with the
resolved name closes that, and the arm worth locking is the unavailable cell — a validator invoked
on the raw text of a formally invalid cell would answer about a value the rest of the theory says
is not readable at all. -/

private def rejection : RegisteredCustomRejection where
  projectCode := "PROJECT_CODE_INVALID"

private def validator : RegisteredCustomFieldValidator := fun value context =>
  if context == explicitCustomFieldValidationContext && value == "ok" then none
  else some rejection

private def world : World where
  now := { epochMillis := 0 }
  customFieldValidator? := fun name =>
    if name == "ProjectCode" then some validator else none

/-- Field 1 is the plain evaluated String; every other id reads empty. -/
private def raw (value : RawCell) : RawFlatContext where
  read id := if id == 1 then value else .empty

private def leafVerdict? (operation : CustomFieldValidityOp) (cell : RawCell) :
    Option Verdict :=
  match elaborateCustomFieldValidityLeaf probeModel world 1 "ProjectCode" operation with
  | .error _ => none
  | .ok leaf => some (leaf.evalAt (probeModel.checkContext (raw cell)) .validation)

/- The registered validator's own answer, both polarities, on a readable value. -/
example : leafVerdict? .valid (.parsed (.str "ok")) = some (.fired .value) := by
  native_decide

example : leafVerdict? .invalid (.parsed (.str "ok")) = some .notFired := by
  native_decide

example : leafVerdict? .valid (.parsed (.str "bad")) = some .notFired := by
  native_decide

/- An absent cell is UNKNOWN before any registry contact, which the value-specified gate owns. -/
example : leafVerdict? .valid .empty = some .unknown := by
  native_decide

/- A **formally invalid** cell — a String declaration holding a parsed number — is UNKNOWN under
   both polarities. What this separates is *reading the checked observation* from *reading the
   stored text*: the wrong implementation hands the validator a value and comes back with a verdict,
   which the `bad` row above shows is a reachable answer here. It does **not** separate malformed
   from absent, and cannot: the value-specified gate maps empty and unavailable alike to UNKNOWN, so
   the two rows agree by design and neither polarity distinguishes them. -/
example : leafVerdict? .valid (.parsed (.num 7)) = some .unknown := by
  native_decide

example : leafVerdict? .invalid (.parsed (.num 7)) = some .unknown := by
  native_decide

end A12Kernel.Conformance.CustomFieldValidityOperand
