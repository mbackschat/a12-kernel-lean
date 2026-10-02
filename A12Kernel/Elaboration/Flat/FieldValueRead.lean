import A12Kernel.Elaboration.Flat.ComputationBinding

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

/-- A category read's refusal of a field declaring no Enumeration, asked once its group gate passed. -/
def FlatFieldDecl.categoryReadRefusal? (declaration : FlatFieldDecl) : Option ResolveError :=
  match declaration.policy.kind with
  | .enumeration => none
  | _ => some (.categoryReadOfNonEnumeration declaration.path)

/-- The refusal a read through `projectionRef` draws once its group gate passed: a stored read's value
    gates, or a category read's non-Enumeration class. -/
def FlatFieldDecl.projectedReadRefusal? (declaration : FlatFieldDecl) :
    EnumerationProjectionRef → Option ResolveError
  | .stored => declaration.fieldValueReadRefusal?
  | .category _ => declaration.categoryReadRefusal?

/-- The field-value read's group gate asked of a failed resolution: a path naming a group draws the
    group class, displacing the field miss a field resolver reports for it. `groupRead` classes such a
    path, since where the read stands decides whether a reader's class answers first. A site whose
    success branch certifies the undisplaced resolution asks this on its failure branch alone. -/
def displaceGroupMiss (miss : ResolveError)
    (groupRead : Unit → Option (GroupPath × Option UnboundOperandLevel)) : ResolveError :=
  if miss.isGroupDisplaceableMiss then
    match groupRead () with
    | some (group, unbound) => .groupInFieldValueRead group unbound miss
    | none => miss
  else
    miss

/-- The field-value read's group gate, `displaceGroupMiss` asked of a resolution. -/
def displaceGroupRead (resolved : Except ResolveError FlatFieldDecl)
    (groupRead : Unit → Option (GroupPath × Option UnboundOperandLevel)) :
    Except ResolveError FlatFieldDecl :=
  resolved.mapError (displaceGroupMiss · groupRead)

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

/-- A rule's read of a field an operator names as a parameter rather than in brackets, which asks the
    group gate alone. A fixed group draws the group class inside `Length`, `RangeAsNumber`,
    `FieldValueAsNumber`, a DateRange bound's field and a scalar membership's subject, and an unstarred
    repeatable group the missing-star class inside `Length` and the membership's subject, the other
    parameters taking it by the same gate. A raw String and a partially known Date meet each
    operator's own gates: `Length` has a raw class of its own, the two conversions refuse both with
    their own classes, and a Date meets the membership's kind gate before any date gate
    ([checkpoint](../../../docs/sources/static-admission-and-class-probes.md#src-field-value-read-predictions)). -/
def FlatModel.resolveEntityRead (model : FlatModel) (declaringGroup : GroupPath)
    (reference : SurfaceFieldPath) (writtenGroup : GroupPath := declaringGroup) :
    Except ResolveError FlatFieldDecl :=
  displaceGroupRead (model.resolveNonrepeatableFieldUnchecked declaringGroup reference writtenGroup)
    (model.ruleGroupRead declaringGroup writtenGroup reference)

/-- A rule's category read `[F -> C]`: the group gate, then a field declaring no Enumeration draws
    the non-Enumeration class ahead of the category's own lookup and of the field's value gates
    ([`kf359`](../../../../a12-rulekit/docs/KERNEL-FINDINGS.md#kf359),
    [checkpoint](../../../docs/sources/static-admission-and-class-probes.md#src-field-value-read-predictions)).
    A raw String, a partially known Date and a full Date all draw that class, so no value gate is
    asked of a category read. -/
def FlatModel.resolveCategoryRead (model : FlatModel) (declaringGroup : GroupPath)
    (reference : SurfaceFieldPath) (writtenGroup : GroupPath := declaringGroup) :
    Except ResolveError FlatFieldDecl := do
  let declaration ← model.resolveEntityRead declaringGroup reference writtenGroup
  match declaration.categoryReadRefusal? with
  | some refusal => throw refusal
  | none => pure declaration

/-- A rule's bracketed read through `projectionRef`: a stored read asks every gate of the
    field-value read, and a category read the group gate alone. -/
def FlatModel.resolveProjectedFieldValueRead (model : FlatModel) (declaringGroup : GroupPath)
    (reference : SurfaceFieldPath) (projectionRef : EnumerationProjectionRef)
    (writtenGroup : GroupPath := declaringGroup) : Except ResolveError FlatFieldDecl :=
  match projectionRef with
  | .stored => model.resolveFieldValueRead declaringGroup reference writtenGroup
  | .category _ => model.resolveCategoryRead declaringGroup reference writtenGroup

/-- Class a computation's read whose path names a group: its target's scope binds the read, so a
    group meets the walk from there before the group class. A level the walk passes, such as the
    target's own group, falls through to the group class, as a rule's does at `refusedReadLevel?`
    ([checkpoint](../../../docs/sources/static-admission-and-class-probes.md#src-field-value-read-predictions)). -/
def FlatModel.computationGroupRead (model : FlatModel) (declaringGroup targetGroup : GroupPath)
    (reference : SurfaceFieldPath) : Unit → Option (GroupPath × Option UnboundOperandLevel) :=
  fun _ => (model.groupNamedBy? declaringGroup reference).map fun group =>
    (group, (model.firstUnboundComputationLevel? declaringGroup targetGroup
      [model.repeatableScopeForGroupPath group]).filter (!·.passesWalk))

/-- A computation's field-value read, bound by its target's scope, whose gates are measured on a String, an
    Enumeration, a Time and a Number target
    ([checkpoint](../../../docs/sources/static-admission-and-class-probes.md#src-field-value-read-carriers)).
    Its target's scope binds its reads, so a group read meets the walk from there before the group
    class: an unstarred repeatable group draws the missing-star class on a Number and a String target
    ([checkpoint](../../../docs/sources/static-admission-and-class-probes.md#src-field-value-read-remaining-sites)). -/
def FlatModel.resolveComputationFieldValueRead (model : FlatModel)
    (declaringGroup targetGroup : GroupPath) (reference : SurfaceFieldPath) :
    Except ResolveError FlatFieldDecl :=
  checkFieldValueRead
    (model.resolveComputationOperandUnchecked declaringGroup targetGroup reference)
    (model.computationGroupRead declaringGroup targetGroup reference)

/-- A computation's read of a field an operator names as a parameter, which asks the group gate alone,
    as `FlatModel.resolveEntityRead` does on a rule. A fixed group draws the group class inside
    `Length`, `FieldValueAsNumber`, `RangeAsNumber` and a DateRange bound's field into a Number target
    and inside `FieldValueAsString` into a String target, and an unstarred repeatable group the
    missing-star class inside `FieldValueAsNumber` and `FieldValueAsString`
    ([checkpoint](../../../docs/sources/static-admission-and-class-probes.md#src-field-value-read-predictions)). -/
def FlatModel.resolveComputationEntityRead (model : FlatModel)
    (declaringGroup targetGroup : GroupPath) (reference : SurfaceFieldPath) :
    Except ResolveError FlatFieldDecl :=
  displaceGroupRead
    (model.resolveComputationOperandUnchecked declaringGroup targetGroup reference)
    (model.computationGroupRead declaringGroup targetGroup reference)

end A12Kernel
