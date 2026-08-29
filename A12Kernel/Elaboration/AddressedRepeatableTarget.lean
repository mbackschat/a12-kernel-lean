import A12Kernel.Elaboration.Flat.Model

/-! # Carrier-neutral repeatable target placement

This module owns the model-relative certificate shared by exact-address computations whose target is repeatable and lies within the computation's declaring group. Carrier-specific target policy remains with each operation.

`GroupPath.isValid` rejects an empty path and any empty segment, so `[]` is not a representable declaring group; `FlatFieldDecl.hasValidPath` applies the same predicate, so no target can sit at `[]` either. That is why validity is checked separately below: `[]` is a prefix of every path, so containment alone would treat the unrepresentable empty group as containing everything. Nothing in `FlatModel` requires the first segment to name a single shared root, so do not read the check as a root convention.

Placement through **this certificate** is containment, not parenthood: the target is admitted from its own group and from any ancestor of it, and refused only from a group it does not lie below. Several exact-address families still carry their own equality-based placement gate and are not governed by this module; [SG4](../../docs/SEMANTICS-GAPS.md#sg4--computation-scheduling-and-state-transition) names them. Do not read this paragraph as an estate-wide rule.

The [declaring-group gate checkpoint](../../docs/SOURCES.md#src-computation-declaring-group-gate) measures both halves against the Kernel, for a bare constant and for the sibling-star operand shape these families use, and separately measures that parent-local correlation is identical from the target's own group, from one ancestor, and from the root. Admission therefore widens without moving any family's correlation clause. That correlation row covers the String sibling-star representative only; other carriers inherit the shared star-axis mechanism rather than their own row.
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
  /-- Containment against `[]` is vacuous, so `targetContained` only means what it says once the
  declaring group is a representable path. This field is what makes the next one load-bearing. -/
  declaringGroupValid : GroupPath.isValid declaringGroup = true
  /-- The target lies at or below the declaring group. Equality is the common case, not the rule. -/
  targetContained : GroupPath.isPrefixOf declaringGroup declaration.groupPath = true
  repeatable : declaration.repeatableScope ≠ []

/-- Check carrier-neutral target placement before an operation checks its own target kind. -/
def checkAddressedRepeatableTarget
    (model : FlatModel) (declaringGroup : GroupPath) (targetField : FieldId) :
    Except AddressedRepeatableTargetElabError
      (CheckedAddressedRepeatableTarget model) :=
  match hTarget : model.lookupUniqueId targetField with
  | .error cause => .error (.target cause)
  | .ok declaration => do
    if hValid : GroupPath.isValid declaringGroup = true then
      if hContained :
          GroupPath.isPrefixOf declaringGroup declaration.groupPath = true then
        if hRepeatable : declaration.repeatableScope.isEmpty then
          throw (.targetNotRepeatable declaration.path)
        else
          pure {
            declaringGroup
            targetField
            declaration
            owned := hTarget
            declaringGroupValid := hValid
            targetContained := hContained
            repeatable := by
              intro empty
              simp [empty] at hRepeatable
          }
      else
        throw (.targetOutsideDeclaringGroup declaration.path declaringGroup)
    else
      throw (.target (.invalidRuleGroup declaringGroup))

end A12Kernel
