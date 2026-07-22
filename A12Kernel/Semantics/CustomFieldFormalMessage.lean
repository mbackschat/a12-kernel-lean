import A12Kernel.Semantics.CustomFieldMessage

/-! # A12Kernel.Semantics.CustomFieldFormalMessage — registered formal-error projection

This capsule projects an already-produced registered custom field rejection into its formal-message payload. The caller owns address resolution, label resolution, and localized fallback selection; the projector owns the exact project code and fixed formal-error metadata.
-/

namespace A12Kernel

/-- The emitted message for one rejected registered custom field value. It remains distinct from authored rule messages even though both expose severity and polarity. -/
structure CustomFieldFormalMessage where
  errorAddress : CellAddr
  errorCode : String
  severity : ValidationSeverity
  messageType : Polarity
  text : ResolvedMessageText
  deriving Repr, DecidableEq

namespace RegisteredCustomRejection

/-- Project a rejection into one VALUE/ERROR formal message. A supplied template, including an empty one, wins over the already-localized fallback. -/
def toFormalMessage (rejection : RegisteredCustomRejection)
    (errorAddress : CellAddr) (resolvedFieldLabel : String)
    (fallbackText : ResolvedMessageText) : CustomFieldFormalMessage where
  errorAddress
  errorCode := rejection.projectCode
  severity := .error
  messageType := .value
  text := (rejection.renderSuppliedMessage? resolvedFieldLabel).getD fallbackText

end RegisteredCustomRejection

end A12Kernel
