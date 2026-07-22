import A12Kernel.Elaboration.CustomField

/-! # A12Kernel.Conformance.CustomFieldElaboration — flat custom declaration locks -/

namespace A12Kernel.Conformance.CustomFieldElaboration

open A12Kernel

private def stringPolicy : FieldPolicy :=
  { kind := .string }

private def numberPolicy : FieldPolicy :=
  { kind := .number { scale := 0, signed := true } }

private def ordinary : FlatFieldDecl :=
  { id := 0, groupPath := ["Order"], name := "Note", policy := stringPolicy }

private def custom (id : FieldId) (fieldName validatorName : String) :
    FlatFieldDecl :=
  {
    id
    groupPath := ["Order"]
    name := fieldName
    policy := stringPolicy
    customType := some { name := validatorName }
  }

private def illegalCustomNumber : FlatFieldDecl :=
  {
    id := 9
    groupPath := ["Order"]
    name := "Count"
    policy := numberPolicy
    customType := some { name := "ProjectCode" }
  }

private def acceptAll : RegisteredCustomFieldValidator := fun _ _ => none

private def world : World where
  now := { epochMillis := 0 }
  customFieldValidator? := fun name =>
    if name == "ProjectCode" || name == "CountryCode" then some acceptAll else none

private def summary (model : FlatModel) :
    Option (Bool × List (FieldId × String)) :=
  match prepareFlatCustomFields world model with
  | .error _ => none
  | .ok prepared => some (prepared.model == model,
      prepared.fields.map fun field =>
        (field.declaration.id, field.customType.declaration.name))

private def errorOf (model : FlatModel) : Option FlatCustomFieldPreparationError :=
  match prepareFlatCustomFields world model with
  | .error error => some error
  | .ok _ => none

/- Ordinary declarations need no custom metadata and preserve the existing model unchanged. -/
example : summary { fields := [ordinary] } = some (true, []) := by
  native_decide

/- Every declared custom String field is retained in model order with its exact resolved name. -/
example :
    summary { fields := [ordinary, custom 1 "Code" "ProjectCode",
      custom 2 "Country" "CountryCode"] } =
      some (true, [(1, "ProjectCode"), (2, "CountryCode")]) := by
  native_decide

/- Custom metadata on a non-String declaration is rejected by ordinary model validation. -/
example : errorOf { fields := [illegalCustomNumber] } =
    some (.model (.customTypeRequiresString ["Order", "Count"])) := by
  native_decide

/- Exact case-sensitive registry resolution happens during preparation, not evaluation. -/
example : errorOf { fields := [custom 1 "Code" "projectcode"] } =
    some (.custom (.missingValidator "projectcode")) := by
  native_decide

end A12Kernel.Conformance.CustomFieldElaboration
