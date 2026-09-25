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

/-- Class a rule's read whose path names a group: it meets the repetition walk as a presence
    operand's does, and past it the group class, which a root group draws too. -/
def FlatModel.ruleGroupRead (model : FlatModel) (declaringGroup writtenGroup : GroupPath)
    (reference : SurfaceFieldPath) : Unit → Option (GroupPath × Option UnboundOperandLevel) :=
  fun _ => (model.groupFieldSlotRefusal? declaringGroup writtenGroup reference).map fun
    | (group, .unboundLevel unbound) => (group, some unbound)
    | (group, _) => (group, none)

/-- A rule's nonrepeatable field-value read. -/
def FlatModel.resolveFieldValueRead (model : FlatModel) (declaringGroup : GroupPath)
    (reference : SurfaceFieldPath) (writtenGroup : GroupPath := declaringGroup) :
    Except ResolveError FlatFieldDecl :=
  checkFieldValueRead (model.resolveNonrepeatableFieldUnchecked declaringGroup reference writtenGroup)
    (model.ruleGroupRead declaringGroup writtenGroup reference)

/-- A rule's category read `[F -> C]`, which asks the group gate alone: a group draws the group
    class ahead of the category reader's refusal of a field without that category
    ([`kf359`](../../../../a12-rulekit/docs/KERNEL-FINDINGS.md#kf359),
    [checkpoint](../../../docs/sources/static-admission-and-class-probes.md#src-field-value-read-carriers)).
    Only an Enumeration declares a category, and no row orders a value gate against that refusal, so
    the value gates are left to the refusal, which projects no class. -/
def FlatModel.resolveCategoryRead (model : FlatModel) (declaringGroup : GroupPath)
    (reference : SurfaceFieldPath) (writtenGroup : GroupPath := declaringGroup) :
    Except ResolveError FlatFieldDecl :=
  displaceGroupRead (model.resolveNonrepeatableFieldUnchecked declaringGroup reference writtenGroup)
    (model.ruleGroupRead declaringGroup writtenGroup reference)

/-- A rule's bracketed read through `projectionRef`: a stored read asks every gate of the
    field-value read, and a category read the group gate alone. -/
def FlatModel.resolveProjectedFieldValueRead (model : FlatModel) (declaringGroup : GroupPath)
    (reference : SurfaceFieldPath) (projectionRef : EnumerationProjectionRef)
    (writtenGroup : GroupPath := declaringGroup) : Except ResolveError FlatFieldDecl :=
  match projectionRef with
  | .stored => model.resolveFieldValueRead declaringGroup reference writtenGroup
  | .category _ => model.resolveCategoryRead declaringGroup reference writtenGroup

/-- A computation's nonrepeatable field-value read, which asks the gates on every target kind
    ([checkpoint](../../../docs/sources/static-admission-and-class-probes.md#src-field-value-read-carriers)).
    Its target's scope binds its reads, so a group read meets the walk from there before the group
    class. The grid reads a fixed group only; a repeatable one is walked on the account the rule's
    read measures, where an unstarred repeatable group draws the missing-star class first. -/
def FlatModel.resolveComputationFieldValueRead (model : FlatModel)
    (declaringGroup targetGroup : GroupPath) (reference : SurfaceFieldPath) :
    Except ResolveError FlatFieldDecl :=
  checkFieldValueRead
    (model.resolveNonrepeatableComputationOperandUnchecked declaringGroup targetGroup reference)
    fun _ => (model.groupNamedBy? declaringGroup reference).map fun group =>
      (group, model.firstUnboundOperandLevel? declaringGroup targetGroup
        [model.repeatableScopeForGroupPath group])

end A12Kernel
