import A12Kernel.Elaboration.StringContext

/-! # A12Kernel.Conformance.CustomFieldContext — prepared flat custom checks -/

namespace A12Kernel.Conformance.CustomFieldContext

open A12Kernel

private def rejection : RegisteredCustomRejection where
  projectCode := "PROJECT_CODE_INVALID"

private def expectedContext : CustomFieldValidationContext where
  locale := "en_US"
  minLength := some 1
  maxLength := some 999
  isDisplayValue := false

private def validator : RegisteredCustomFieldValidator := fun value context =>
  if value == "accepted" && context == expectedContext then none else some rejection

private def world : World where
  now := { epochMillis := 0 }
  customFieldValidator? := fun name =>
    if name == "ProjectCode" then some validator else none

private def customCode : FlatFieldDecl :=
  {
    id := 1
    groupPath := ["Order"]
    name := "Code"
    policy := { kind := .string }
    customType := some { name := "ProjectCode" }
  }

private def ordinaryNote : FlatFieldDecl :=
  { id := 2, groupPath := ["Order"], name := "Note",
    policy := { kind := .string },
    stringPolicy := { lineBreaksPermitted := true } }

private def count : FlatFieldDecl :=
  { id := 3, groupPath := ["Order"], name := "Count",
    policy := { kind := .number { scale := 0, signed := true } } }

private def model : FlatModel :=
  { fields := [customCode, ordinaryNote, count] }

private def observe (id : FieldId) (rawCell : RawCell) : CellObservation :=
  match prepareFlatCustomFields world model with
  | .error _ => .unknown .malformed
  | .ok prepared =>
      let raw : RawFlatContext := {
        read := fun candidate => if candidate == id then rawCell else .empty
      }
      (prepared.checkContext "en_US" raw).observeValidationAt id

private def observeUnpreparedCustom (rawCell : RawCell) : CellObservation :=
  let raw : RawFlatContext := {
    read := fun candidate => if candidate == customCode.id then rawCell else .empty
  }
  (model.checkContext raw).observeValidationAt customCode.id

/- Prepared custom String fields preserve accepted values and exact registered rejection causes. -/
example : observe 1 (.parsed (.str "accepted")) = .value (.str "accepted") := by
  native_decide

example : observe 1 (.parsed (.str "rejected")) =
    .unknown (.registeredCustomValidation rejection) := by
  native_decide

/- The ordinary context builder must fail closed instead of bypassing unresolved custom metadata. -/
example : observeUnpreparedCustom (.parsed (.str "accepted")) =
    .unknown .malformed := by
  native_decide

/- Physical/semantic emptiness and prior parser rejection retain ordinary cell semantics. -/
example : observe 1 .empty = .empty := by
  native_decide

example : observe 1 (.parsed (.str "")) = .empty := by
  native_decide

example : observe 1 (.rejected .unsupportedCharacter) =
    .unknown .unsupportedCharacter := by
  native_decide

/- A custom String declaration fails closed on an incoherent heterogeneous raw value. -/
example : observe 1 (.parsed (.num 7)) = .unknown .malformed := by
  native_decide

/- Declarations without custom metadata still use the existing ordinary formal checker. -/
example : observe 2 (.parsed (.str "A\r\nB")) = .value (.str "A\nB") := by
  native_decide

example : observe 3 (.parsed (.num 7)) = .value (.num 7) := by
  native_decide

/- Unknown IDs retain the established malformed fail-closed result. -/
example : observe 99 (.parsed (.str "accepted")) = .unknown .malformed := by
  native_decide

private def forgedOtherType : CheckedCustomFieldType where
  declaration := { name := "OtherType" }
  validator := fun _ _ => none

private def forgedCustomObservation : CellObservation :=
  let prepared : PreparedFlatCustomFields model := {
    fields := [{ declaration := customCode, customType := forgedOtherType }] }
  let raw : RawFlatContext := {
    read := fun candidate =>
      if candidate == customCode.id then .parsed (.str "accepted") else .empty }
  (prepared.checkContext "en_US" raw).observeValidationAt customCode.id

/- Copying the flat declaration cannot attach a checker resolved for another registered custom type. -/
example : forgedCustomObservation = .unknown .malformed := by
  native_decide

end A12Kernel.Conformance.CustomFieldContext
