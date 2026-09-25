import A12Kernel.Elaboration.Flat.Model

/-! # The field-value read's gates

The field-value read `[…]` is one grammar production, and the Kernel asks its gates as the bracket
closes, whatever construct stands around it
([checkpoint](../../../docs/sources/static-admission-and-class-probes.md#src-field-value-read-grid)).
This module owns them once, so a bracket site asks them after its own resolution instead of carrying
a copy. A starred bracket is not spelled by `SurfaceFieldPath`, so the star gate
has no surface here.
-/

namespace A12Kernel

/-- The value gates of the field-value read `[…]`, asked of the declaration it resolved to: a raw
    String and a partially known Date are each refused a value read
    ([checkpoint](../../../docs/sources/static-admission-and-class-probes.md#src-field-value-read-grid)). -/
def FlatFieldDecl.fieldValueReadRefusal? (declaration : FlatFieldDecl) : Option ResolveError :=
  if declaration.isRawString then some (.rawFieldValueRead declaration.path)
  else if declaration.isPartiallyKnownDate then some (.partialDateFieldValueRead declaration.path)
  else none

/-- The field-value read's group gate: a path naming a group draws the group class, displacing the
    field miss a field resolver reports for it. `groupRead` classes such a path, since where the read
    stands decides whether a reader's class answers first. -/
def displaceGroupRead (resolved : Except ResolveError FlatFieldDecl)
    (groupRead : Unit → Option (GroupPath × Option UnboundOperandLevel)) :
    Except ResolveError FlatFieldDecl :=
  match resolved with
  | .error miss =>
      if miss.isGroupDisplaceableMiss then
        match groupRead () with
        | some (group, unbound) => .error (.groupInFieldValueRead group unbound miss)
        | none => .error miss
      else
        .error miss
  | other => other

/-- The gates the field-value read `[…]` asks of the entity it names once its bracket closes, after
    the reader's own classes ([`kf473`](../../../../a12-rulekit/docs/KERNEL-FINDINGS.md#kf473),
    [checkpoint](../../../docs/sources/static-admission-and-class-probes.md#src-field-value-read-grid)):
    the group gate, then the two value gates. A caller reading two operands checks the first before
    resolving the second, which is why the Kernel names the left read's class. -/
def checkFieldValueRead (resolved : Except ResolveError FlatFieldDecl)
    (groupRead : Unit → Option (GroupPath × Option UnboundOperandLevel)) :
    Except ResolveError FlatFieldDecl := do
  let declaration ← displaceGroupRead resolved groupRead
  match declaration.fieldValueReadRefusal? with
  | some refusal => throw refusal
  | none => pure declaration

/-- A rule's nonrepeatable field-value read. A group read meets the repetition walk as a presence
    operand's does, and past it the group class, which a root group draws too. -/
def FlatModel.resolveFieldValueRead (model : FlatModel) (declaringGroup : GroupPath)
    (reference : SurfaceFieldPath) (writtenGroup : GroupPath := declaringGroup) :
    Except ResolveError FlatFieldDecl :=
  checkFieldValueRead (model.resolveNonrepeatableFieldUnchecked declaringGroup reference writtenGroup)
    fun _ => (model.groupFieldSlotRefusal? declaringGroup writtenGroup reference).map fun
      | (group, .unboundLevel unbound) => (group, some unbound)
      | (group, _) => (group, none)

end A12Kernel
