import A12Kernel.Semantics.CustomFieldMessage

/-! # A12Kernel.Conformance.CustomFieldMessage — registered rejection message locks -/

namespace A12Kernel.Conformance.CustomFieldMessage

open A12Kernel

private def rejection (template : Option String) : RegisteredCustomRejection where
  projectCode := "PROJECT_CODE_INVALID"
  messageTemplate := template

/- The absent supplied template stays absent so the caller can select its formal-message fallback. -/
example : (rejection none).renderSuppliedMessage? "Account" = none := by
  native_decide

/- A present empty template remains an explicitly supplied empty message. -/
example : (rejection (some "")).renderSuppliedMessage? "Account" =
    some { text := "" } := by
  native_decide

/- Every exact token is replaced, while all surrounding bytes retain their order. -/
example :
    RegisteredCustomRejection.renderSuppliedMessage?
        (rejection (some "Invalid $<fieldName>$ / $<fieldName>$!")) "Account" =
      some { text := "Invalid Account / Account!" } := by
  native_decide

/- Replacement bytes are opaque: token-looking label text is not rescanned. -/
example :
    RegisteredCustomRejection.renderSuppliedMessage?
        (rejection (some "$<fieldName>$")) "$<fieldName>$ label" =
      some { text := "$<fieldName>$ label" } := by
  native_decide

/- Only the exact case-sensitive literal token is special. -/
example :
    RegisteredCustomRejection.renderSuppliedMessage?
        (rejection (some "$<fieldname>$ $fieldName$ $<fieldName>")) "Account" =
      some { text := "$<fieldname>$ $fieldName$ $<fieldName>" } := by
  native_decide

/- An empty resolved label removes each exact token without changing other bytes. -/
example :
    RegisteredCustomRejection.renderSuppliedMessage?
        (rejection (some "<$<fieldName>$>|$<fieldName>$")) "" =
      some { text := "<>|" } := by
  native_decide

end A12Kernel.Conformance.CustomFieldMessage
