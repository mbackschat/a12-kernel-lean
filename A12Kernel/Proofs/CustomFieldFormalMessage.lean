import A12Kernel.Semantics.CustomFieldFormalMessage
import A12Kernel.Proofs.CustomFieldType

/-! # A12Kernel.Proofs.CustomFieldFormalMessage — registered formal-message laws -/

namespace A12Kernel

/-- Absence selects the caller's exact fallback without interpreting its bytes. -/
theorem customFieldFormalMessage_absent_exact
    (projectCode resolvedFieldLabel : String) (errorAddress : MessagePointer)
    (fallbackText : ResolvedMessageText) :
    RegisteredCustomRejection.toFormalMessage
        { projectCode, messageTemplate := none }
        errorAddress resolvedFieldLabel fallbackText = {
      errorAddress
      errorCode := projectCode
      severity := .error
      messageType := .value
      text := fallbackText
    } := by
  rfl

/-- A supplied template wins over the fallback and has exactly the fixed-token renderer's result. -/
theorem customFieldFormalMessage_supplied_exact
    (projectCode template resolvedFieldLabel : String)
    (errorAddress : MessagePointer) (fallbackText : ResolvedMessageText) :
    RegisteredCustomRejection.toFormalMessage
        { projectCode, messageTemplate := some template }
        errorAddress resolvedFieldLabel fallbackText = {
      errorAddress
      errorCode := projectCode
      severity := .error
      messageType := .value
      text := {
        text := template.replace RegisteredCustomRejection.fieldNameToken
          resolvedFieldLabel
      }
    } := by
  rfl

/-- Address, project code, severity, and polarity never depend on message selection. -/
theorem customFieldFormalMessage_metadata_exact
    (rejection : RegisteredCustomRejection) (errorAddress : MessagePointer)
    (resolvedFieldLabel : String) (fallbackText : ResolvedMessageText) :
    let message := rejection.toFormalMessage errorAddress resolvedFieldLabel fallbackText
    message.errorAddress = errorAddress ∧
      message.errorCode = rejection.projectCode ∧
      message.severity = .error ∧
      message.messageType = .value := by
  simp [RegisteredCustomRejection.toFormalMessage]

/-- The leading blocking registered cause is recovered without changing any project payload. -/
theorem checkedCell_registeredCustomRejection_head
    (rejection : RegisteredCustomRejection) (rest : List FormalCause)
    (parsed : Option α) (rawPresent : Bool) :
    ({
      rawPresent := rawPresent
      parsed := parsed
      findings := .registeredCustomValidation rejection :: rest
    } :
      CheckedCell α).registeredCustomRejection? = some rejection := by
  rfl

/-- Another leading formal cause cannot manufacture a registered custom message. -/
theorem checkedCell_nonCustomCause_hasNoRegisteredRejection
    (parsed : Option α) (rawPresent : Bool) (rest : List FormalCause) :
    ({
      rawPresent := rawPresent
      parsed := parsed
      findings := .malformed :: rest
    } :
      CheckedCell α).registeredCustomRejection? = none := by
  rfl

@[simp]
theorem customFieldValidationOutput_nonrelevant
    (checked : CheckedCustomFieldType) (locale : String)
    (raw : RawCell String) (errorAddress : MessagePointer)
    (resolvedFieldLabel : String) (fallbackText : ResolvedMessageText) :
    checked.checkRelevantWithMessage locale false raw errorAddress
      resolvedFieldLabel fallbackText = none := by
  rfl

/-- One validator rejection supplies both the exact checked cell and the formal message derived from that same cause. -/
theorem customFieldValidationOutput_rejection_exact
    (checked : CheckedCustomFieldType) (locale value : String)
    (rejection : RegisteredCustomRejection)
    (errorAddress : MessagePointer) (resolvedFieldLabel : String)
    (fallbackText : ResolvedMessageText)
    (nonempty : value.isEmpty = false)
    (rejected : checked.validator value
      (checked.declaration.validationContext locale) = some rejection)
    (unavailable : rejection.admitsValue = false) :
    checked.checkRelevantWithMessage locale true (.parsed value) errorAddress
        resolvedFieldLabel fallbackText = some {
      cell := {
        rawPresent := true
        parsed := none
        findings := [.registeredCustomValidation rejection]
      }
      message? := some (rejection.toFormalMessage errorAddress
        resolvedFieldLabel fallbackText)
    } := by
  rw [CheckedCustomFieldType.checkRelevantWithMessage,
    customFieldType_rejection_exact checked locale value rejection nonempty rejected unavailable]
  rfl

/-- A report-only custom result projects the same formal message while retaining its readable cell. -/
theorem customFieldValidationOutput_report_exact
    (checked : CheckedCustomFieldType) (locale value : String)
    (rejection : RegisteredCustomRejection)
    (errorAddress : MessagePointer) (resolvedFieldLabel : String)
    (fallbackText : ResolvedMessageText)
    (nonempty : value.isEmpty = false)
    (reported : checked.validator value
      (checked.declaration.validationContext locale) = some rejection)
    (admitted : rejection.admitsValue = true) :
    checked.checkRelevantWithMessage locale true (.parsed value) errorAddress
        resolvedFieldLabel fallbackText = some {
      cell := {
        rawPresent := true
        parsed := some (normalizeEvaluatedString value)
        findings := []
        reports := [.registeredCustomValidation rejection]
      }
      message? := some (rejection.toFormalMessage errorAddress resolvedFieldLabel fallbackText)
    } := by
  rw [CheckedCustomFieldType.checkRelevantWithMessage,
    customFieldType_report_exact checked locale value rejection nonempty reported admitted]
  rfl

/-- Acceptance retains the evaluated String and has no custom formal message. -/
theorem customFieldValidationOutput_acceptance_exact
    (checked : CheckedCustomFieldType) (locale value : String)
    (errorAddress : MessagePointer) (resolvedFieldLabel : String)
    (fallbackText : ResolvedMessageText)
    (nonempty : value.isEmpty = false)
    (accepted : checked.validator value
      (checked.declaration.validationContext locale) = none) :
    checked.checkRelevantWithMessage locale true (.parsed value) errorAddress
        resolvedFieldLabel fallbackText = some {
      cell := {
        rawPresent := true
        parsed := some (normalizeEvaluatedString value)
        findings := []
      }
      message? := none
    } := by
  simp [CheckedCustomFieldType.checkRelevantWithMessage,
    CheckedCustomFieldType.checkRelevantRaw, nonempty, accepted,
    CheckedCustomFieldType.checkStringRaw, CheckedCustomFieldType.classifyString,
    CheckedCell.registeredCustomRejection?, CheckedCell.formalReports]

/-- Abort-mode ingestion can be composed across field batches without discarding either batch's formal reports. -/
theorem customFieldValidationMode_abort_append
    (left right : List CustomFieldValidationOutput) :
    CustomFieldValidationMode.abortOnFormalErrors.continuesAfterIngestion (left ++ right) =
      (CustomFieldValidationMode.abortOnFormalErrors.continuesAfterIngestion left &&
        CustomFieldValidationMode.abortOnFormalErrors.continuesAfterIngestion right) := by
  simp [CustomFieldValidationMode.continuesAfterIngestion, List.all_append]

/-- A readable custom report is still a formal error for abort-mode continuation (spec/06 A.3). -/
theorem customFieldValidationMode_readable_report_stops_abort
    (value : String) (rejection : RegisteredCustomRejection) :
    let output : CustomFieldValidationOutput := {
      cell := {
        rawPresent := true
        parsed := some value
        findings := []
        reports := [.registeredCustomValidation rejection] }
      message? := none }
    observeCell .validation output.cell = .value value ∧
      CustomFieldValidationMode.abortOnFormalErrors.continuesAfterIngestion [output] = false := by
  simp [CustomFieldValidationMode.continuesAfterIngestion, CheckedCell.formalReports,
    observeCell]

end A12Kernel
