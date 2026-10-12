import A12Kernel.Semantics.CustomFieldFormalMessage

/-! # A12Kernel.Conformance.CustomFieldFormalMessage — registered formal-message locks -/

namespace A12Kernel.Conformance.CustomFieldFormalMessage

open A12Kernel

private def address : MessagePointer :=
  MessagePointer.ofCellAddr { field := 7, path := [2, 4] }

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

private def checkedValidator : RegisteredCustomFieldValidator := fun value _ =>
  if value == "accepted" then none
  else some (rejection (some "Invalid $<fieldName>$"))

private def checkedWorld : World where
  now := { epochMillis := 0 }
  customFieldValidator? := fun name =>
    if name == "ProjectCode" then some checkedValidator else none

private def checkedOutput (relevant : Bool) (raw : RawCell String)
    (world : World := checkedWorld) :
    Option CustomFieldValidationOutput :=
  match elaborateCustomFieldType world { name := "ProjectCode" } with
  | .error _ => none
  | .ok checked =>
      checked.checkRelevantWithMessage "en_US" relevant raw address
        "Account" fallback

/- One rejected check result supplies both the exact reusable cell and its projected custom message. -/
example : checkedOutput true (.parsed "rejected") = some {
    cell := {
      rawPresent := true
      parsed := none
      findings := [.registeredCustomValidation
        (rejection (some "Invalid $<fieldName>$"))]
    }
    message? := some {
      errorAddress := address
      errorCode := "PROJECT_CODE_INVALID"
      severity := .error
      messageType := .value
      text := { text := "Invalid Account" }
    }
  } := by
  native_decide

/- Accepted, empty, and previously rejected inputs retain their checked cell but never manufacture a custom rejection message. -/
example : (checkedOutput true (.parsed "accepted")).map (·.message?) =
    some none := by
  native_decide

example : (checkedOutput true .empty).map (·.message?) = some none := by
  native_decide

example : checkedOutput true (.rejected .malformed) = some {
    cell := {
      rawPresent := true
      parsed := none
      findings := [.malformed]
    }
    message? := none
  } := by
  native_decide

/- Nonrelevance excludes the entire output before validator sampling or message projection. -/
example : checkedOutput false (.parsed "rejected") = none := by
  native_decide

private def reportedRejection : RegisteredCustomRejection := {
  projectCode := "testIDNummer", messageTemplate := some "Test $<fieldName>$" }

private def reportedWorld : World where
  now := { epochMillis := 0 }
  customFieldValidator? := fun name =>
    if name == "ProjectCode" then some (fun _ _ => some reportedRejection) else none

example : checkedOutput true (.parsed "A\r\nB") reportedWorld = some {
    cell := {
      rawPresent := true, parsed := some "A\nB", findings := [],
      reports := [.registeredCustomValidation reportedRejection] }
    message? := some {
      errorAddress := address, errorCode := "testIDNummer", severity := .error,
      messageType := .value, text := { text := "Test Account" } } } := by
  native_decide

example :
    CustomFieldValidationMode.fullExamination.continuesAfterIngestion
      ((checkedOutput true (.parsed "ABCD") reportedWorld).toList) = true ∧
    CustomFieldValidationMode.abortOnFormalErrors.continuesAfterIngestion
      ((checkedOutput true (.parsed "ABCD") reportedWorld).toList) = false := by native_decide

private def continuationPair (relevant : Bool) (raw : RawCell String)
    (world : World := checkedWorld) : Bool × Bool :=
  let outputs := (checkedOutput relevant raw world).toList
  (CustomFieldValidationMode.fullExamination.continuesAfterIngestion outputs,
    CustomFieldValidationMode.abortOnFormalErrors.continuesAfterIngestion outputs)

example : [
    continuationPair true (.parsed "accepted"),
    continuationPair true (.parsed "reported") reportedWorld,
    continuationPair true (.parsed "rejected"),
    continuationPair true .empty,
    continuationPair true .presentEmpty,
    continuationPair false (.parsed "rejected")] = [
      (true, true), (true, false), (true, false),
      (true, true), (true, true), (true, true)] := by native_decide

example : (checkedOutput true .empty).map (·.cell.rawPresent) = some false ∧
    (checkedOutput true .presentEmpty).map (·.cell.rawPresent) = some true ∧
    checkedOutput false (.parsed "reported") reportedWorld = none := by native_decide

end A12Kernel.Conformance.CustomFieldFormalMessage
