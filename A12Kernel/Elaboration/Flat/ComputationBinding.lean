import A12Kernel.Elaboration.Flat.Model

/-! # Computation operand binding

A computation binds its operands by its target's scope rather than by the group declaring it
([`spec/09`](../../../spec/09-computations.md) §5): an operand is admitted exactly when that scope binds
every repeatable level it crosses. This module owns that rule once for every computation carrier.
-/

namespace A12Kernel

/-- One model field's repeatable scope, empty for a field the model does not own. -/
def FlatModel.fieldRepeatableScope (model : FlatModel) (field : FieldId) : List RepeatableLevel :=
  match model.lookupUniqueId field with
  | .ok declaration => declaration.repeatableScope
  | .error _ => []

/-- The unbound level a computation's operand binding scopes are refused at: the levels its target's
    scope holds are bound and only the rest are asked, so a fixed target binds none. -/
def FlatModel.firstUnboundComputationLevel? (model : FlatModel) (declaringGroup targetGroup : GroupPath)
    (scopes : List (List RepeatableLevel)) : Option UnboundOperandLevel :=
  let bound := model.repeatableScopeForGroupPath targetGroup
  model.firstUnboundOperandLevel? declaringGroup targetGroup (scopes.map (·.filter (!bound.contains ·)))

/-- Resolve an operand of a computation after a caller has validated the model, refusing one that
crosses a level its target's scope leaves unbound wherever the computation is declared, with the class
the target's position and that level select
([checkpoint](../../../docs/sources/group-list-and-capacity-probes.md#src-computation-star-binding-gate)). -/
def FlatModel.resolveComputationOperandUnchecked (model : FlatModel)
    (declaringGroup targetGroup : GroupPath) (reference : SurfaceFieldPath) :
    Except ResolveError FlatFieldDecl := do
  let declaration ← model.resolveFieldDeclarationUnchecked declaringGroup reference
  match model.firstUnboundComputationLevel? declaringGroup targetGroup [declaration.repeatableScope] with
  | none => pure declaration
  | some unbound => throw (.unboundOperandLevel declaration.path unbound)

end A12Kernel
