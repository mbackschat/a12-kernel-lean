import A12Kernel.Elaboration.CheckedGroupPresence
import A12Kernel.Semantics.Required

/-! # Model-certified absolute-required staging -/

namespace A12Kernel

inductive CheckedRequiredError where
  | model (error : ResolveError)
  | notRequired (path : List String)
  | requiresGroupGate (path : List String) (groupPath : GroupPath)
  deriving Repr, DecidableEq

namespace CheckedDocument

/-- Resolve one absolute nonrepeatable required target from the checked document's exact model, evaluate its generated mandatory rule against the immutable base cells, and return the separate authored-validation view. -/
def applyAbsoluteRequiredAt (checked : CheckedDocument model)
    (field : FieldId) : Except CheckedRequiredError AbsoluteRequiredResult := do
  let declaration ← model.lookupUniqueId field |>.mapError .model
  let scope ← model.requirednessScopeFor declaration |>.mapError .model
  match scope with
  | none => throw (.notRequired declaration.path)
  | some .absolute =>
      pure (applyAbsoluteRequired declaration.toPresenceField checked.flatContext)
  | some (.relativeTo groupPath) =>
      throw (.requiresGroupGate declaration.path groupPath)

end CheckedDocument

end A12Kernel
