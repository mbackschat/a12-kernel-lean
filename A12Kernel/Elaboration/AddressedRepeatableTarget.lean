import A12Kernel.Elaboration.Flat.Model

/-! # Carrier-neutral repeatable target placement

This module owns the model-relative certificate shared by exact-address computations whose target is repeatable and belongs to the computation's declaring group. Carrier-specific target policy remains with each operation.
-/

namespace A12Kernel

inductive AddressedRepeatableTargetElabError where
  | target (cause : ResolveError)
  | targetOutsideDeclaringGroup (path declaringGroup : GroupPath)
  | targetNotRepeatable (path : List String)
  deriving Repr, DecidableEq

/-- One model-owned repeatable target in its declaring group, before any carrier-specific admission. -/
structure CheckedAddressedRepeatableTarget (model : FlatModel) where
  private mk ::
  declaringGroup : GroupPath
  targetField : FieldId
  declaration : FlatFieldDecl
  owned : model.lookupUniqueId targetField = .ok declaration
  inDeclaringGroup : declaration.groupPath = declaringGroup
  repeatable : declaration.repeatableScope ≠ []

/-- Check carrier-neutral target placement before an operation checks its own target kind. -/
def checkAddressedRepeatableTarget
    (model : FlatModel) (declaringGroup : GroupPath) (targetField : FieldId) :
    Except AddressedRepeatableTargetElabError
      (CheckedAddressedRepeatableTarget model) :=
  match hTarget : model.lookupUniqueId targetField with
  | .error cause => .error (.target cause)
  | .ok declaration => do
    if hGroup : declaration.groupPath = declaringGroup then
      if hRepeatable : declaration.repeatableScope.isEmpty then
        throw (.targetNotRepeatable declaration.path)
      else
        pure {
          declaringGroup
          targetField
          declaration
          owned := hTarget
          inDeclaringGroup := hGroup
          repeatable := by
            intro empty
            simp [empty] at hRepeatable
        }
    else
      throw (.targetOutsideDeclaringGroup declaration.path declaringGroup)

end A12Kernel
