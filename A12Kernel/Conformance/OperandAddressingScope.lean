import A12Kernel.Elaboration.OperandAddressingScope
import A12Kernel.Elaboration.Flat.Model

/-! # Locks on the operand addressing and scope gates

Five of the seven classes are measured
([sweep](../../docs/sources/diagnostic-class-vocabulary-and-sweeps.md#src-parser-static-legality-sweep), [membership row](../../docs/sources/diagnostic-class-vocabulary-and-sweeps.md#src-table-enumeration-inertness)); the relative-step star's lenient
arm is read from the guard, and the shared-root-group class is argued unreachable from an A12 model by a
source enumeration re-derived in the owning module.

The matrix separates the two star gates by their disagreement over lenience, both edges of the
parent-path membership test, the depth split between the two unresolvable-name classes, and the
shared-root-group guard's dependence on its caller's world.
-/

namespace A12Kernel.Conformance.OperandAddressingScope

open A12Kernel

private def starKey? (lenient : Bool) (position : WildcardPosition) : Option String :=
  (wildcardPlacementRefusal lenient position).map KernelStaticDiagnostic.kernelCode

private def scopeKey? (scope : EntityPath) (members : List EntityPath) : Option String :=
  (groupScopeRefusal scope members).map KernelStaticDiagnostic.kernelCode

private def rootKey? (hModelCaller : Bool) (roots : List String) : Option String :=
  (sharedRootGroupRefusal hModelCaller roots).map KernelStaticDiagnostic.kernelCode

/- **The two star gates disagree about lenience.** One flag moved across both positions: the relative
   step's refusal disappears under a lenient parse while the rule context's stands, so a lenient consumer
   and a strict one disagree on exactly one of the two. -/
example :
    starKey? false .relativeStep = some "MVK_INVALID_WILDCARD_REL" ∧
      starKey? true .relativeStep = none ∧
      starKey? false .ruleContext = some "MVK_INVALID_WILDCARD_FOR_RULEGROUP" ∧
      starKey? true .ruleContext = some "MVK_INVALID_WILDCARD_FOR_RULEGROUP" := by
  native_decide

/- **The star-required and repeatability guards, both ways.** -/
example :
    wildcardRequirementRefusal false = some .wildcardsRequired ∧
      wildcardRequirementRefusal true = none ∧
      repeatableGroupRefusal false = some .groupNotRepeatable ∧
      repeatableGroupRefusal true = none := by
  native_decide

/- **Membership admits a descendant at any depth.** A direct child and a grandchild of the scoping group
   are both inside, which is what stops the test being read as "direct children only". -/
example :
    scopeKey? ["R1", "G"] [["R1", "G", "A"]] = none ∧
      scopeKey? ["R1", "G"] [["R1", "G", "H", "B"]] = none ∧
      scopeKey? ["R1", "G"] [["R1", "G", "A"], ["R1", "G", "H", "B"]] = none := by
  native_decide

/- **Its other edge: the scoping group itself is outside**, because its own parent lies above the scope.
   Replays the measured refusal of a field beside the group rather than under it. -/
example :
    scopeKey? ["R1", "G"] [["R1", "A"]] = some "MVK_NOT_IN_GROUP" ∧
      scopeKey? ["R1", "G"] [["R1", "G"]] = some "MVK_NOT_IN_GROUP" ∧
      scopeKey? ["R1", "G"] [["R2", "G", "A"]] = some "MVK_NOT_IN_GROUP" := by
  native_decide

/- **A sibling whose name merely starts with the group's is outside**, the segment-boundary case a raw
   string prefix would get wrong. -/
example :
    scopeKey? ["R1", "G"] [["R1", "GX", "A"]] = some "MVK_NOT_IN_GROUP" := by
  native_decide

/- **One offending member refuses the whole list**, and an empty list is admitted. -/
example :
    scopeKey? ["R1", "G"] [["R1", "G", "A"], ["R1", "A"]] = some "MVK_NOT_IN_GROUP" ∧
      scopeKey? ["R1", "G"] [] = none := by
  native_decide

/- **The unresolvable name splits by depth, not by fault.** A one-segment candidate reports the
   root-group class and a deeper one the entity class, from the identical failure. -/
example :
    (unresolvedNameRefusal ["Nope"]).kernelCode = "MVK_INVALID_ROOT_GROUP" ∧
      (unresolvedNameRefusal ["R1", "Nope"]).kernelCode = "MVK_INVALID_ENTITY" ∧
      (unresolvedNameRefusal ["R1", "G", "Nope"]).kernelCode = "MVK_INVALID_ENTITY" := by
  native_decide

/- **The shared-root-group guard only speaks for an H-model caller.** The same disagreeing roots are
   silent from an A12 call site, which is the modelled form of its unreachability; agreeing roots and a
   singleton are admitted from either. -/
example :
    rootKey? true ["R1", "R2"] = some "MVK_DIFFERENT_ROOT_GROUPS" ∧
      rootKey? false ["R1", "R2"] = none ∧
      rootKey? true ["R1", "R1"] = none ∧
      rootKey? true ["R1"] = none := by
  native_decide

private def resolverModel : FlatModel :=
  { fields := [{ id := 1, groupPath := ["Item"], name := "Title", policy := { kind := .string } }] }

private def resolveKey? (reference : SurfaceFieldPath) : Option String :=
  match resolverModel.resolveFieldDeclarationUnchecked ["Item"] reference with
  | .ok _ => none
  | .error error => error.diagnostic?.map KernelStaticDiagnostic.kernelCode

/- **The shared field resolver draws the same four classes on every carrier measured**, so they are
   the resolver's and belong on its projection: an unknown root segment, an unknown name below a known
   root, an unknown bare name, and a parent walk above the root. The resolved control projects nothing
   ([checkpoint](../../docs/sources/static-admission-and-class-probes.md#src-resolver-failure-classes-every-carrier)). -/
example :
    resolveKey? { base := .absolute, groups := ["Item"], field := "Nope" } =
        some "MVK_INVALID_ENTITY" ∧
      resolveKey? { base := .absolute, groups := ["Nope"], field := "Title" } =
        some "MVK_INVALID_ROOT_GROUP" ∧
      resolveKey? { base := .absolute, groups := ["Nope", "Deeper"], field := "Title" } =
        some "MVK_INVALID_ROOT_GROUP" ∧
      resolveKey? { base := .absolute, groups := ["Item", "Nope"], field := "Title" } =
        some "MVK_INVALID_ENTITY" ∧
      -- A lone segment is still read as a root before the path's missing field is judged, while a
      -- lone declared root is a group in a field slot, whose class each carrier chooses.
      resolveKey? { base := .absolute, groups := [], field := "Nope" } =
        some "MVK_INVALID_ROOT_GROUP" ∧
      resolveKey? { base := .absolute, groups := [], field := "Item" } = none ∧
      resolveKey? { base := .relative 0, groups := [], field := "Nope" } =
        some "MVK_INVALID_ENTITY" ∧
      resolveKey? { base := .relative 1, groups := [], field := "Title" } =
        some "MVK_TOO_MANY_PARENT_GROUPS" ∧
      resolveKey? { base := .absolute, groups := ["Item"], field := "Title" } = none := by
  native_decide

end A12Kernel.Conformance.OperandAddressingScope
