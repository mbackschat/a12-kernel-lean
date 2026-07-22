import A12Kernel.Semantics.CustomFieldValidity

/-! # A12Kernel.Conformance.CustomFieldValidity — explicit registered validity locks -/

namespace A12Kernel.Conformance.CustomFieldValidity

open A12Kernel

private def rejection : RegisteredCustomRejection where
  projectCode := "PROJECT_CODE_INVALID"

private def explicitContext : CustomFieldValidationContext where
  locale := "de_DE"
  minLength := none
  maxLength := none
  isDisplayValue := false

private def validator : RegisteredCustomFieldValidator := fun value context =>
  if context == explicitContext && value == "ok" then none else some rejection

private def world : World where
  now := { epochMillis := 0 }
  customFieldValidator? := fun name =>
    if name == "ProjectCode" then some validator else none

private def evaluate (operation : CustomFieldValidityOp)
    (observation : CellObservation String) : Option Verdict :=
  match elaborateCustomFieldValidity world "ProjectCode" with
  | .error _ => none
  | .ok checked => some (checked.eval operation observation)

/- Explicit Valid/Invalid use absent bounds and fixed German stored-value context. -/
example : evaluate .valid (.value "ok") = some (.fired .value) := by
  native_decide

example : evaluate .invalid (.value "ok") = some .notFired := by
  native_decide

example : evaluate .valid (.value "bad") = some .notFired := by
  native_decide

example : evaluate .invalid (.value "bad") = some (.fired .value) := by
  native_decide

/- Empty and formally unavailable operands stay UNKNOWN and do not become invalid. -/
example : evaluate .valid .empty = some .unknown := by
  native_decide

example : evaluate .invalid (.unknown .malformed) = some .unknown := by
  native_decide

example : evaluate .invalid (.value "") = some .unknown := by
  native_decide

/- Checked construction resolves the exact registered name and rejects absence. -/
example :
    (match elaborateCustomFieldValidity world "projectcode" with
    | .error (.missingValidator "projectcode") => true
    | _ => false) = true := by
  native_decide

/- The declared-field path still supplies present effective bounds through the same context type. -/
example :
    CustomFieldTypeDeclaration.validationContext
        { name := "ProjectCode" } "en_US" = {
      locale := "en_US"
      minLength := some 1
      maxLength := some 999
      isDisplayValue := false
    } := by
  native_decide

end A12Kernel.Conformance.CustomFieldValidity
