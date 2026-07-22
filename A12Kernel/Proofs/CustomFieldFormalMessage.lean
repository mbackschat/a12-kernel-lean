import A12Kernel.Semantics.CustomFieldFormalMessage

/-! # A12Kernel.Proofs.CustomFieldFormalMessage — registered formal-message laws -/

namespace A12Kernel

/-- Absence selects the caller's exact fallback without interpreting its bytes. -/
theorem customFieldFormalMessage_absent_exact
    (projectCode resolvedFieldLabel : String) (errorAddress : CellAddr)
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
    (errorAddress : CellAddr) (fallbackText : ResolvedMessageText) :
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
    (rejection : RegisteredCustomRejection) (errorAddress : CellAddr)
    (resolvedFieldLabel : String) (fallbackText : ResolvedMessageText) :
    let message := rejection.toFormalMessage errorAddress resolvedFieldLabel fallbackText
    message.errorAddress = errorAddress ∧
      message.errorCode = rejection.projectCode ∧
      message.severity = .error ∧
      message.messageType = .value := by
  simp [RegisteredCustomRejection.toFormalMessage]

end A12Kernel
