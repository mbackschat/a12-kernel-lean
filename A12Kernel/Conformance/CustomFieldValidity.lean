import A12Kernel.Semantics.CustomFieldValidity

/-! # A12Kernel.Conformance.CustomFieldValidity — explicit validity locks over a partial registry

The separating axes are registration state × fill state × polarity, which is the matrix the kernel was measured on. -/

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

/- Checked construction resolves the exact registered name; a differently cased name is a
   legal miss rather than an error. -/
example :
    (match elaborateCustomFieldValidity world "ProjectCode" with
    | .ok { name := "ProjectCode", validator? := some _ } => true
    | _ => false) = true := by
  native_decide

example :
    (match elaborateCustomFieldValidity world "projectcode" with
    | .ok { name := "projectcode", validator? := none } => true
    | _ => false) = true := by
  native_decide

/- The model check's only name requirement is nonemptiness. -/
example :
    (match elaborateCustomFieldValidity world "" with
    | .error .emptyTypeName => true
    | _ => false) = true := by
  native_decide

/-! ## Unsupplied validator

The model check does not consult the host registry, so an unregistered name is admitted and
its runtime behaviour is degenerate rather than rejected. -/

private def evaluateUnsupplied (operation : CustomFieldValidityOp)
    (observation : CellObservation String) : Option Verdict :=
  match elaborateCustomFieldValidity world "NoSuchType" with
  | .error _ => none
  | .ok checked => some (checked.eval operation observation)

/- Both polarities fire VALUE on the same filled value, so they are not complements here. -/
example : evaluateUnsupplied .valid (.value "ok") = some (.fired .value) := by
  native_decide

example : evaluateUnsupplied .invalid (.value "ok") = some (.fired .value) := by
  native_decide

/- The value-specified gate decides before any registry contact, so an empty field is
   registration-blind. -/
example : evaluateUnsupplied .valid .empty = some .unknown := by
  native_decide

example : evaluateUnsupplied .invalid (.value "") = some .unknown := by
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
