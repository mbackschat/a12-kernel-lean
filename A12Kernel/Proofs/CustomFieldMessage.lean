import A12Kernel.Semantics.CustomFieldMessage

/-! # A12Kernel.Proofs.CustomFieldMessage — supplied registered rejection message laws -/

namespace A12Kernel

/-- Missing validator text remains distinguishable from an explicitly supplied message. -/
@[simp]
theorem customFieldMessage_absent (projectCode resolvedFieldLabel : String) :
    RegisteredCustomRejection.renderSuppliedMessage?
        { projectCode, messageTemplate := none } resolvedFieldLabel = none := by
  rfl

/-- A supplied template has exactly the standard one-pass fixed-token replacement result. -/
theorem customFieldMessage_supplied_exact
    (projectCode template resolvedFieldLabel : String) :
    RegisteredCustomRejection.renderSuppliedMessage?
        { projectCode, messageTemplate := some template } resolvedFieldLabel =
      some {
        text := template.replace RegisteredCustomRejection.fieldNameToken
          resolvedFieldLabel
      } := by
  rfl

/-- The project error code cannot influence rendering of the supplied template. -/
theorem customFieldMessage_projectCode_irrelevant
    (firstCode secondCode : String) (template : Option String)
    (resolvedFieldLabel : String) :
    RegisteredCustomRejection.renderSuppliedMessage?
        { projectCode := firstCode, messageTemplate := template }
        resolvedFieldLabel =
      RegisteredCustomRejection.renderSuppliedMessage?
        { projectCode := secondCode, messageTemplate := template }
        resolvedFieldLabel := by
  cases template <;> rfl

end A12Kernel
