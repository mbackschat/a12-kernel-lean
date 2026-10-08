import A12Kernel.Elaboration.StaticDiagnostic

/-! # Finding the one index group above a referenced entity, and the three ways that fails

A repeatable group may declare an **index field**, the cell whose value identifies a row rather than
its physical position. Two constructs need to know which index field governs a reference — the
semantic index, and the parallel-iteration join — and both reach it the same way: walk **upward**
from the referenced entity through its containing groups, and require that exactly one group on that
path declares an index.

**The walk is order-sensitive and only the innermost index group is fully examined.** Each ancestor
that declares an index is checked, in inside-out order. The first one found has its *count* of
declared names checked and then becomes the answer; a second one found anywhere above refuses
immediately, **without examining its own count**. So a path whose inner group declares one name and
whose outer group declares three reports the two-groups class, and the same two groups swapped report
the several-names class. One nesting, two spellings, two classes.

**The name is resolved only after the walk clears.** The declared name is looked up inside the
resolved group and must name a *field* there; a name that resolves to a group draws the same class as
one that resolves to nothing. Because this runs after the walk, a path that already refuses never
reports the name class however bad its names are — a consumer resolving names as it walks reports a
class the Kernel does not.

**A path with no index group at all is not a refusal.** It resolves to nothing, and the calling
construct decides what to do with that; the classes here are about ambiguity and broken declarations,
never about absence.

**Evidence.** The two-groups class is measured, separated against two admitted controls on one model:
a field two index-declaring groups deep drew it under a parallel-iterating condition, the same
condition against a field only one index group deep is admitted, and the same field under a
non-parallel condition is admitted because the walk never runs
([checkpoint](../../docs/sources/model-structure-and-declaration-probes.md#src-index-group-resolution)). The other two have no witness
through this project's carrier, for two different **measured** reasons: the A12 model format carries
a single index-field *name* rather than a list, so a group declaring several fails DM-JSON
deserialization; and a name that resolves to nothing makes the model fail to build before any
condition is checked, so the walk is never reached. Neither is recorded as unreachable — both are
stated as the total function the Kernel computes, with the carrier's limit named.

This module carries no rendered message text, by the licensing boundary in [`CLAUDE.md`](../../CLAUDE.md).
-/

namespace A12Kernel

/-- One group on the upward path, as far as index resolution reads it. -/
structure IndexDeclaringGroup where
  /-- How many index-field names the group declares. Zero means it is not an index group and the
  walk passes straight over it. -/
  declaredNames : Nat := 0
  /-- Whether the declared name resolves to a field of this group. Read **only** once the group has
  become the resolved index group, which is why a group the walk never settles on may carry a broken
  name without consequence. -/
  nameResolvesToField : Bool := true
  deriving Repr, DecidableEq

/-- Whether this group declares an index at all. -/
def IndexDeclaringGroup.declaresIndex (group : IndexDeclaringGroup) : Bool :=
  group.declaredNames != 0

/-- **The upward walk.** `found` carries the innermost index group already settled on. The path is
ordered **innermost first**, matching the direction the Kernel walks; reversing it is a different
model and can be a different class. -/
def indexGroupWalk (found : Option IndexDeclaringGroup) :
    List IndexDeclaringGroup → Except KernelStaticDiagnostic (Option IndexDeclaringGroup)
  | [] => .ok found
  | group :: outer =>
      if !group.declaresIndex then indexGroupWalk found outer
      else match found with
        | some _ => .error .multipleIndexFields
        | none =>
            if group.declaredNames > 1 then .error .multipleIndexFields2
            else indexGroupWalk (some group) outer

/-- **Both stages.** The walk settles on at most one index group, and only then is that group's
declared name resolved. Absence of any index group is a clear result, not a refusal. -/
def indexResolution (path : List IndexDeclaringGroup) :
    Except KernelStaticDiagnostic (Option IndexDeclaringGroup) :=
  match indexGroupWalk none path with
  | .error refusal => .error refusal
  | .ok none => .ok none
  | .ok (some group) =>
      if group.nameResolvesToField then .ok (some group) else .error .indexFieldInvalid

/-- The class a path reports, or `none` when resolution succeeds either way. -/
def indexResolutionRefusal (path : List IndexDeclaringGroup) : Option KernelStaticDiagnostic :=
  match indexResolution path with
  | .error refusal => some refusal
  | .ok _ => none

/-- The index group resolution settles on, or `none` both when the path declares no index and when
resolution refused. A consumer needs [`indexResolutionRefusal`](#A12Kernel.indexResolutionRefusal)
beside it to tell those two apart. -/
def resolvedIndexGroup? (path : List IndexDeclaringGroup) : Option IndexDeclaringGroup :=
  match indexResolution path with
  | .error _ => none
  | .ok found => found

/-- The index groups on a path, innermost first. The walk's whole subject. -/
def indexDeclaringGroups (path : List IndexDeclaringGroup) : List IndexDeclaringGroup :=
  path.filter IndexDeclaringGroup.declaresIndex

end A12Kernel
