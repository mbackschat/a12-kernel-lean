import A12Kernel.Elaboration.Flat.Model

/-! # Carrier-neutral repeatable target placement

This module owns the model-relative certificate shared by exact-address computations whose target is repeatable and sits directly in the computation's declaring group. Carrier-specific target policy remains with each operation.

`inDeclaringGroup` demands **equality**, which is deliberately narrower than the Kernel. The Kernel's gate is containment: a repeatable target is admitted from its own group and from any ancestor of it, refused only from a group it does not lie below. The [declaring-group gate checkpoint](../../docs/SOURCES.md#src-computation-declaring-group-gate) measures both, including the sibling-star operand shape these families use, whose ancestor declaration the Kernel admits once the relative operand is re-spelled for that base.

The restriction stays because admission is not the whole clause. Every consuming family evaluates parent-local correlation against the declaring group, and no measurement covers that runtime under an ancestor declaration; widening the certificate would let each family apply a correlation clause to inputs it was never calibrated on. Widen it only together with that runtime measurement, per [SG4](../../docs/SEMANTICS-GAPS.md#sg4--computation-scheduling-and-state-transition).
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
