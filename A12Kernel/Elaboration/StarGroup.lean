import A12Kernel.Elaboration.StarPath
import A12Kernel.Semantics.GroupPresence

/-! # Checked terminal-repeatable group-star consumers

This capsule resolves a sole starred group path whose terminal group is repeatable, counts its concrete topology-produced rows, and feeds that one structural count to the two legal starred group predicates and `NumberOfFilledGroups`. It is a full-validation boundary: mixed starred/plain operand lists, descendant-cell admission, partial group relevance, nonrepeatable terminal groups, filters, and whole-rule orchestration remain outside.
-/

namespace A12Kernel

/-- A parser-independent group path retaining every authored wildcard marker. -/
structure SurfaceStarGroupPath where
  base : PathBase
  groups : List SurfaceStarGroupSegment
  deriving Repr, DecidableEq

inductive StarredGroupElabError where
  | resolve (error : ResolveError)
  | invalidGroupReference (reference : SurfaceStarGroupPath)
  | path (error : StarPathElabError)
  | incoherentCore
  deriving Repr, DecidableEq

/-- One terminal repeatable group and the shared checked plan that reaches each of its concrete rows exactly once. -/
structure CheckedStarredGroupSource (model : FlatModel) where
  group : RepeatableGroupDecl
  path : StarPath
  modelWellFormed : model.validate.isOk = true
  groupOwned : model.repeatableGroups.contains group = true
  ancestryOwned : path.axes.map (·.level) = model.repeatableScopeForGroupPath group.path
  firstStarWithin : path.firstStar < path.axes.length
  pathValid : path.validate.isOk = true

private def SurfaceStarGroupPath.resolveAgainst (reference : SurfaceStarGroupPath)
    (declaringGroup : GroupPath) : Except StarredGroupElabError (GroupPath × GroupPath) := do
  if !GroupPath.isValid declaringGroup then
    throw (.resolve (.invalidRuleGroup declaringGroup))
  if reference.groups.isEmpty || !reference.groups.all fun segment => !segment.name.isEmpty then
    throw (.invalidGroupReference reference)
  let basePath ← match reference.base with
    | .absolute => pure []
    | .relative parents =>
        GroupPath.walkUp declaringGroup parents |>.mapError .resolve
  let groupPath := basePath ++ reference.groups.map (·.name)
  if GroupPath.isValid groupPath then pure (basePath, groupPath)
  else throw (.invalidGroupReference reference)

/-- Resolve one legal terminal-repeatable starred group through the same model-derived star planner used by checked field stars. -/
def elaborateStarredGroupSource (model : FlatModel) (declaringGroup : GroupPath)
    (source : SurfaceStarGroupPath) :
    Except StarredGroupElabError (CheckedStarredGroupSource model) :=
  match hModel : model.validate with
  | .error error => .error (.resolve error)
  | .ok () => do
      let (basePath, groupPath) ← source.resolveAgainst declaringGroup
      let group ← model.lookupUniqueRepeatablePath groupPath |>.mapError .resolve
      let plan ← elaborateStarPathPlan model basePath source.groups group.path |>.mapError .path
      if hGroup : model.repeatableGroups.contains group = true then
        if hAncestry : plan.path.axes.map (·.level) =
            model.repeatableScopeForGroupPath group.path then
          pure {
            group
            path := plan.path
            modelWellFormed := by rw [hModel]; rfl
            groupOwned := hGroup
            ancestryOwned := hAncestry
            firstStarWithin := plan.firstStarWithin
            pathValid := plan.pathValid }
        else
          throw .incoherentCore
      else
        throw .incoherentCore

/-- The only group-list predicates for which the kernel admits a starred group operand. -/
inductive StarredGroupFillQuantifier where
  | noGroupFilled
  | atLeastOneGroupFilled
  deriving Repr, DecidableEq

def StarredGroupFillQuantifier.toGroupFillQuantifier :
    StarredGroupFillQuantifier → GroupFillQuantifier
  | .noGroupFilled => .noGroupFilled
  | .atLeastOneGroupFilled => .atLeastOneGroupFilled

/-- Every instantiated terminal row is structural group content, including a created-but-empty or over-limit row. -/
def StarredGroupFillQuantifier.evalCount (operator : StarredGroupFillQuantifier)
    (count : Nat) : ValidationFillOutcome :=
  operator.toGroupFillQuantifier.evalTally {
    filled := count, empty := 0, unavailable := 0 }

namespace CheckedStarredGroupSource

/-- Resolve the canonical nested topology once, retaining its exact terminal-row environments. -/
def resolvedTopology (checked : CheckedStarredGroupSource model)
    (document : Document) (outer : Env) : Except StarAddressingError ResolvedStarTopology :=
  checked.path.resolve document outer

/-- Count concrete terminal repeatable rows without consulting descendant cells. -/
def rowCount (checked : CheckedStarredGroupSource model)
    (document : Document) (outer : Env) : Except StarAddressingError Nat := do
  let resolved ← checked.resolvedTopology document outer
  pure resolved.environments.length

/-- Evaluate either legal sole-star group predicate from the shared structural row count. -/
def evaluateFull (checked : CheckedStarredGroupSource model)
    (operator : StarredGroupFillQuantifier) (document : Document) (outer : Env) :
    Except StarAddressingError ValidationFillOutcome := do
  pure (operator.evalCount (← checked.rowCount document outer))

/-- The sole-star numeric form is always available after checked topology succeeds and counts the same concrete terminal rows. -/
def numberOfFilledGroups (checked : CheckedStarredGroupSource model)
    (document : Document) (outer : Env) : Except StarAddressingError FilledGroupCount := do
  pure (.value (← checked.rowCount document outer))

end CheckedStarredGroupSource

end A12Kernel
