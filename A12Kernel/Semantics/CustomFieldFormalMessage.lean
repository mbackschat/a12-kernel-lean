import A12Kernel.Semantics.CustomFieldMessage
import A12Kernel.Semantics.MessagePointer

/-! # A12Kernel.Semantics.CustomFieldFormalMessage — registered formal-error projection

This capsule projects an already-produced registered custom field rejection into its formal-message payload. The caller owns address resolution, label resolution, and localized fallback selection; the projector owns the exact project code and fixed formal-error metadata.
-/

namespace A12Kernel

/-- The emitted message for one rejected registered custom field value. It remains distinct from authored rule messages even though both expose severity and polarity. -/
structure CustomFieldFormalMessage where
  errorAddress : MessagePointer
  errorCode : String
  severity : ValidationSeverity
  messageType : Polarity
  text : ResolvedMessageText
  deriving Repr, DecidableEq

/-- One relevance-gated declared custom field result. The checked cell remains the reusable semantic observation; `message?` is only its registered-rejection formal projection. -/
structure CustomFieldValidationOutput where
  cell : CheckedCell String
  message? : Option CustomFieldFormalMessage
  deriving Repr, DecidableEq

/-- The two evidenced core validation modes differ in continuation after custom ingestion; value admission is independent (spec/06 A.3). -/
inductive CustomFieldValidationMode where
  | fullExamination
  | abortOnFormalErrors
  deriving Repr, DecidableEq

/-- Decide the custom-ingestion contribution to continuation in the modern A12 profile. Both reserved reports and unavailable values are formal errors; other field families retain their own formal gates. -/
def CustomFieldValidationMode.continuesAfterIngestion (mode : CustomFieldValidationMode)
    (outputs : List CustomFieldValidationOutput) : Bool :=
  match mode with
  | .fullExamination => true
  | .abortOnFormalErrors => outputs.all (·.cell.formalReports.isEmpty)

namespace CheckedCell

/-- Recover the leading reported custom finding without mistaking its message for value unavailability (spec/06 A.3). -/
def registeredCustomRejection? (cell : CheckedCell α) :
    Option RegisteredCustomRejection :=
  match cell.formalReports.head? with
  | some (.registeredCustomValidation rejection) => some rejection
  | _ => none

end CheckedCell

namespace RegisteredCustomRejection

/-- Project a rejection into one VALUE/ERROR formal message. A supplied template, including an empty one, wins over the already-localized fallback. -/
def toFormalMessage (rejection : RegisteredCustomRejection)
    (errorAddress : MessagePointer) (resolvedFieldLabel : String)
    (fallbackText : ResolvedMessageText) : CustomFieldFormalMessage where
  errorAddress
  errorCode := rejection.projectCode
  severity := .error
  messageType := .value
  text := (rejection.renderSuppliedMessage? resolvedFieldLabel).getD fallbackText

end RegisteredCustomRejection

namespace CheckedCustomFieldType

/-- Check one relevant raw value once, retain that exact cell, and derive its optional registered custom formal message without resampling the validator. -/
def checkRelevantWithMessage (checked : CheckedCustomFieldType)
    (locale : String) (relevant : Bool) (raw : RawCell String)
    (errorAddress : MessagePointer) (resolvedFieldLabel : String)
    (fallbackText : ResolvedMessageText) : Option CustomFieldValidationOutput :=
  (checked.checkRelevantRaw locale relevant raw).map fun cell => {
    cell
    message? := cell.registeredCustomRejection?.map fun rejection =>
      rejection.toFormalMessage errorAddress resolvedFieldLabel fallbackText
  }

end CheckedCustomFieldType

end A12Kernel
