import A12Kernel.Semantics.CustomFieldFormalMessage

/-! # A12Kernel.Conformance.CustomFieldFormalMessage — registered formal-message locks -/

namespace A12Kernel.Conformance.CustomFieldFormalMessage

open A12Kernel

private def address : CellAddr :=
  { field := 7, path := [2, 4] }

private def fallback : ResolvedMessageText :=
  { text := "The value is invalid." }

private def rejection (template : Option String) : RegisteredCustomRejection where
  projectCode := "PROJECT_CODE_INVALID"
  messageTemplate := template

/- Absent validator text selects the caller's exact localized fallback. -/
example :
    RegisteredCustomRejection.toFormalMessage
        (rejection none) address "Account" fallback = {
      errorAddress := address
      errorCode := "PROJECT_CODE_INVALID"
      severity := .error
      messageType := .value
      text := fallback
    } := by
  native_decide

/- A supplied template wins even when it explicitly renders to empty text. -/
example :
    (RegisteredCustomRejection.toFormalMessage
        (rejection (some "")) address "Account" fallback).text =
      { text := "" } := by
  native_decide

/- Supplied text receives the already-resolved label while address and project code remain exact. -/
example :
    RegisteredCustomRejection.toFormalMessage
        (rejection (some "Invalid $<fieldName>$")) address "Account" fallback = {
      errorAddress := address
      errorCode := "PROJECT_CODE_INVALID"
      severity := .error
      messageType := .value
      text := { text := "Invalid Account" }
    } := by
  native_decide

/- An already-resolved fallback is opaque and is not interpreted as a custom template. -/
example :
    (RegisteredCustomRejection.toFormalMessage
        (rejection none) address "Account"
        { text := "Fallback $<fieldName>$" }).text =
      { text := "Fallback $<fieldName>$" } := by
  native_decide

end A12Kernel.Conformance.CustomFieldFormalMessage
