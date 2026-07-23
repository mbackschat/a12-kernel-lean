import A12Kernel.Elaboration.CheckedGroupPresence
import A12Kernel.Semantics.Required

/-! # Model-certified absolute-required staging -/

namespace A12Kernel

namespace CheckedDocument

/-- Resolve one absolute nonrepeatable required target from the checked document's exact model, evaluate its generated mandatory rule against the immutable base cells, and return the separate authored-validation view. -/
def applyAbsoluteRequiredAt (checked : CheckedDocument model)
    (field : FieldId) : Except ResolveError AbsoluteRequiredResult := do
  let declaration ← model.resolveNonrepeatableDeclarationById field
  pure (applyAbsoluteRequired declaration.toPresenceField checked.flatContext)

end CheckedDocument

end A12Kernel
