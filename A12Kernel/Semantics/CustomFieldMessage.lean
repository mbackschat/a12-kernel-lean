import A12Kernel.Semantics.CustomFieldType
import A12Kernel.Semantics.ValidationRule

/-! # A12Kernel.Semantics.CustomFieldMessage — supplied registered rejection text

Registered custom field validators may supply one raw message template with exactly one special literal token. This capsule consumes an already-resolved field label and produces resolved text; label-provider invocation and caller-owned fallback selection stay outside.
-/

namespace A12Kernel

namespace RegisteredCustomRejection

/-- The sole placeholder recognized inside a registered custom field rejection template. -/
def fieldNameToken : String :=
  "$<fieldName>$"

/-- Render a supplied custom rejection template once. `String.replace` scans the original template, so inserted label bytes are opaque rather than recursively interpreted. Absence remains absence for the caller's fallback path. -/
def renderSuppliedMessage? (rejection : RegisteredCustomRejection)
    (resolvedFieldLabel : String) : Option ResolvedMessageText :=
  rejection.messageTemplate.map fun template =>
    { text := template.replace fieldNameToken resolvedFieldLabel }

end RegisteredCustomRejection

end A12Kernel
