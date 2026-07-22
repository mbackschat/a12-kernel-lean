import A12Kernel.Semantics.CustomFieldType

/-! # A12Kernel.Conformance.CustomFieldType — registered validator observation locks -/

namespace A12Kernel.Conformance.CustomFieldType

open A12Kernel

private def rejection (code : String := "PROJECT_CODE_INVALID") :
    RegisteredCustomRejection where
  projectCode := code
  messageTemplate := some "Invalid $<fieldName>$"

private def declaration (minimum maximum : Option Nat) :
    CustomFieldTypeDeclaration where
  name := "ProjectCode"
  minLength := minimum
  maxLength := maximum

private def expectedContext (locale : String) (minimum maximum : Nat) :
    CustomFieldValidationContext where
  locale := locale
  minLength := minimum
  maxLength := maximum
  isDisplayValue := false

private def validatorExpecting (expected : CustomFieldValidationContext) :
    RegisteredCustomFieldValidator := fun value actual =>
  if actual == expected then
    if value == "ok" then none else some rejection
  else
    some (rejection "WRONG_CONTEXT")

private def worldWith (validator : RegisteredCustomFieldValidator) : World where
  now := { epochMillis := 0 }
  customFieldValidator? := fun name =>
    if name == "ProjectCode" then some validator else none

private def causeOf (world : World) (decl : CustomFieldTypeDeclaration)
    (locale : String) (relevant : Bool) (raw : RawCell String) :
    Option FormalCause :=
  match elaborateCustomFieldType world decl with
  | .error _ => none
  | .ok checked =>
      (checked.checkRelevantRaw locale relevant raw).bind
        (fun cell => cell.findings.head?)

private def phasePair (world : World) (decl : CustomFieldTypeDeclaration)
    (locale value : String) : Option (CellObservation String × CellObservation String) :=
  match elaborateCustomFieldType world decl with
  | .error _ => none
  | .ok checked =>
      (checked.checkRelevantRaw locale true (.parsed value)).map
        (fun cell => (observeCell .validation cell, observeCell .computation cell))

/- Authored and defaulted bounds, locale, and stored-value mode reach the registered validator exactly. -/
example :
    causeOf (worldWith (validatorExpecting (expectedContext "de_DE" 3 5)))
      (declaration (some 3) (some 5)) "de_DE" true (.parsed "bad") =
      some (.registeredCustomValidation rejection) := by
  native_decide

example :
    causeOf (worldWith (validatorExpecting (expectedContext "en_US" 1 999)))
      (declaration none none) "en_US" true (.parsed "bad") =
      some (.registeredCustomValidation rejection) := by
  native_decide

/- Empty and nonrelevant cells are excluded before validator sampling. -/
example :
    causeOf (worldWith (validatorExpecting (expectedContext "de_DE" 3 5)))
      (declaration (some 3) (some 5)) "de_DE" true .empty = none := by
  native_decide

example :
    (match elaborateCustomFieldType
      (worldWith (validatorExpecting (expectedContext "de_DE" 3 5)))
      (declaration (some 3) (some 5)) with
    | .ok checked =>
        (checked.checkRelevantRaw "de_DE" false (.parsed "bad")).isNone
    | .error _ => false) = true := by
  native_decide

/- Accepted input stays clean; a preceding parser rejection wins without reinterpretation. -/
example :
    causeOf (worldWith (validatorExpecting (expectedContext "de_DE" 3 5)))
      (declaration (some 3) (some 5)) "de_DE" true (.parsed "ok") = none := by
  native_decide

example :
    causeOf (worldWith (validatorExpecting (expectedContext "de_DE" 3 5)))
      (declaration (some 3) (some 5)) "de_DE" true (.rejected .malformed) =
      some .malformed := by
  native_decide

/- One returned checked cell supplies the exact project rejection to both phases. -/
example :
    phasePair (worldWith (validatorExpecting (expectedContext "de_DE" 3 5)))
      (declaration (some 3) (some 5)) "de_DE" "bad" =
      some (.unknown (.registeredCustomValidation rejection),
        .poison (.registeredCustomValidation rejection)) := by
  native_decide

/- A missing registered name is a checked-construction failure, not acceptance or generic rejection. -/
example :
    (match elaborateCustomFieldType { now := { epochMillis := 0 } }
      (declaration none none) with
    | .error (.missingValidator "ProjectCode") => true
    | _ => false) = true := by
  native_decide

end A12Kernel.Conformance.CustomFieldType
