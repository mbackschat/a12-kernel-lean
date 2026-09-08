import A12Kernel.Elaboration.StaticDiagnostic

/-! # Where a condition's operand may point, and where its star may sit

Seven parser guards constrain an operand's *address* rather than its kind: three about the wildcard's
placement, three about the scope a list of entities must share, and one about what an unresolvable name
reports. They are grouped here because each is a small independent predicate over one reference, raised
by a different checker, and because two pairs of them disagree in ways a single "scope rule" would hide.

**The two star refusals disagree about lenience, and that is this module's sharpest fact.** A wildcard
attached to a relative upward step is refused under a strict parse and **admitted under a lenient one**;
a wildcard on the rule's own context group is refused unconditionally. So a lenient importer and a strict
one see different vocabularies from the same model, and only one of the two gates moves.

**Repeatability is asked of the group's own lowest level.** A group nested under a repeatable ancestor is
not itself repeatable for this purpose, so the guard is not satisfied by inherited repetition.

**Scope membership is a parent-path prefix test, which fixes both of its edges.** A member's parent path
must lie under the scoping group, so a descendant at any depth is inside — and the scoping group itself
is *outside*, because its own parent is one level up. Neither edge follows from "the entity is in the
group" read informally.

**An unresolvable name reports one of two classes by depth, not by fault.** At root-group depth it is
`MVK_INVALID_ROOT_GROUP`; one segment deeper the identical failure is `MVK_INVALID_ENTITY`. The two
partition a single condition, so a consumer treating them as different diagnoses is reading a distinction
that is not there.

**Evidence.** The star-on-rule-context, star-required, `@From` repeatability, group-membership and
root-group classes are measured
([checkpoint](../../docs/SOURCES.md#src-static-admission-class-sweep)); the relative-step star's rule is
stated in [`spec/08`](../../spec/08-paths-and-references.md) and its **lenient** arm is read from the
guard rather than measured, no probe here authoring a lenient parse.
`MVK_DIFFERENT_ROOT_GROUPS` is **unreachable from an A12 model** by source enumeration re-derived here:
its emitter `checkAllEntitiesInSameRootGroup` has exactly two callers in the whole tracked parser tree,
both under the `hdv` H-model packages. That is a negative existential over a searched surface, so it
carries the same recall limit as any other — a reflective or generated caller would escape the search.

This module carries no rendered message text, by the licensing boundary in [`CLAUDE.md`](../../CLAUDE.md).
-/

namespace A12Kernel

/-- Where a wildcard was written, for the two guards that read one. -/
inductive WildcardPosition where
  /-- On a relative upward step. -/
  | relativeStep
  /-- On the rule's own context group. -/
  | ruleContext
  deriving Repr, DecidableEq

/-- **The two star placements, and the lenience they disagree about.** -/
def wildcardPlacementRefusal (lenient : Bool) : WildcardPosition → Option KernelStaticDiagnostic
  | .relativeStep => if lenient then none else some .wildcardOnRelativeStep
  | .ruleContext => some .wildcardOnRuleContext

/-- An operator that requires a starred operand, given whether the operand carries one. -/
def wildcardRequirementRefusal (operandHasWildcard : Bool) : Option KernelStaticDiagnostic :=
  if operandHasWildcard then none else some .wildcardsRequired

/-- **Repeatability at the group's own lowest level**, which inherited repetition does not supply. -/
def repeatableGroupRefusal (repeatableOnLowestLevel : Bool) : Option KernelStaticDiagnostic :=
  if repeatableOnLowestLevel then none else some .groupNotRepeatable

/-- A path as a list of name segments, root first. -/
abbrev EntityPath := List String

/-- **Scope membership**, as the Kernel tests it: the member's *parent* path must lie strictly under the
scoping group. Written over the parent rather than the member so both edges come out right — a
descendant at any depth is inside, and the group itself is not. -/
def withinGroup (scope member : EntityPath) : Bool :=
  scope.isPrefixOf member.dropLast

/-- The group-scoped list guard, refusing at its first member outside the scope. -/
def groupScopeRefusal (scope : EntityPath) (members : List EntityPath) :
    Option KernelStaticDiagnostic :=
  if members.all (withinGroup scope) then none else some .entityNotInGroup

/-- **The shared-root-group guard.** Reachable only from the H-model call sites, which this clause states
by taking the caller's world as an argument rather than by omitting the class. -/
def sharedRootGroupRefusal (hModelCaller : Bool) (roots : List String) :
    Option KernelStaticDiagnostic :=
  if !hModelCaller then none
  else match roots with
    | [] => none
    | first :: rest => if rest.all (· == first) then none else some .entitiesInDifferentRootGroups

/-- **The unresolvable-name partition.** One failure, two classes, chosen by the candidate's depth. -/
def unresolvedNameRefusal (candidate : EntityPath) : KernelStaticDiagnostic :=
  if candidate.length ≤ 1 then .invalidRootGroup else .invalidEntity

end A12Kernel
