import A12Kernel.Elaboration.StarPath
import A12Kernel.Semantics.GroupPresence
import A12Kernel.Semantics.NumericComparison

/-! # Checked group-star consumers

This capsule resolves a starred group path through the shared model-derived topology. A terminal repeatable group retains the established structural-row interpretation used by the two legal group predicates and `NumberOfFilledGroups`; partial numeric counting applies the local reduced-universal group-path account that reproduces the measured fifth outcome pattern. A nonrepeatable terminal retains its exact group path so checked validation can derive the existing descendant-content/error product once per topology-produced environment. Partial predicate relevance, filters, computation's ordered scan, and whole-rule orchestration remain outside.
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
  | unknownGroup (path : GroupPath)
  /-- The named group carries no field anywhere in its subtree. The Kernel admits such a group in a
  model and then refuses every operand naming it, on a code of its own rather than the unknown-group
  one. Only a repeatable group reaches this here, because `FlatModel` represents a nonrepeatable group
  solely through its fields. -/
  | groupHasNoFields (path : GroupPath)
  | path (error : StarPathElabError)
  | incoherentCore
  deriving Repr, DecidableEq

/-- One terminal repeatable group and the shared checked plan that reaches each of its concrete rows exactly once. -/
structure CheckedStarredGroupSource (model : FlatModel) where
  declaringGroup : GroupPath
  group : RepeatableGroupDecl
  path : StarPath
  modelWellFormed : model.validate.isOk = true
  groupOwned : model.repeatableGroups.contains group = true
  /-- The terminal carries at least one field, which is the Kernel's group-operand gate rather than a
  structural property of the path. -/
  groupPopulated : model.groupContributesField group.path = true
  ancestryOwned : path.axes.map (·.level) = model.repeatableScopeForGroupPath group.path
  firstStarWithin : path.firstStar < path.axes.length
  pathValid : path.validate.isOk = true

/-- Partial starred-group counting distinguishes an unavailable group extent from the exact in-capacity structural row count. -/
inductive PartialValidationFilledGroupCountResult where
  | nonRelevant
  | evaluated (count : FilledGroupCount)
  deriving Repr, DecidableEq

/-- One nonrepeatable terminal group reached through a shared checked star plan. Its concrete presence remains the existing descendant-derived group product, not structural row count. -/
structure CheckedStarredGroupPresenceSource (model : FlatModel) where
  declaringGroup : GroupPath
  groupPath : GroupPath
  path : StarPath
  modelWellFormed : model.validate.isOk = true
  groupOwned : model.hasGroupPath groupPath = true
  terminalNonrepeatable :
    model.repeatableGroups.any (fun group => group.path == groupPath) = false
  ancestryOwned :
    path.axes.map (·.level) = model.repeatableScopeForGroupPath groupPath
  firstStarWithin : path.firstStar < path.axes.length
  pathValid : path.validate.isOk = true

/-- The two terminal interpretations admitted by one authored starred group operand. -/
inductive CheckedStarredGroupOperandSource (model : FlatModel) where
  | terminalRepeatable (source : CheckedStarredGroupSource model)
  | terminalPresence (source : CheckedStarredGroupPresenceSource model)

/-- Base resolution can fail only in these two ways. Keeping it a separate closed type makes
    a planner diagnostic unrepresentable at this step instead of merely unreached. -/
inductive StarredGroupBaseError where
  | resolve (error : ResolveError)
  | invalidGroupReference (reference : SurfaceStarGroupPath)
  deriving Repr, DecidableEq

def StarredGroupBaseError.toElabError :
    StarredGroupBaseError → StarredGroupElabError
  | .resolve error => .resolve error
  | .invalidGroupReference reference => .invalidGroupReference reference

/-- Resolve only the base prefix. The caller composes the full group path from this base and
    the authored segments, so no separate equation is needed to relate the two. -/
private def SurfaceStarGroupPath.resolveBase (reference : SurfaceStarGroupPath)
    (declaringGroup : GroupPath) : Except StarredGroupBaseError GroupPath := do
  if !GroupPath.isValid declaringGroup then
    throw (.resolve (.invalidRuleGroup declaringGroup))
  if reference.groups.isEmpty || !reference.groups.all fun segment => !segment.name.isEmpty then
    throw (.invalidGroupReference reference)
  let basePath ← match reference.base with
    | .absolute => pure []
    | .relative parents =>
        GroupPath.walkUp declaringGroup parents |>.mapError .resolve
  if GroupPath.isValid (basePath ++ reference.groups.map (·.name)) then pure basePath
  else throw (.invalidGroupReference reference)

/-- Resolve one legal terminal-repeatable starred group through the same model-derived star planner used by checked field stars. -/
def elaborateStarredGroupSource (model : FlatModel) (declaringGroup : GroupPath)
    (source : SurfaceStarGroupPath) :
    Except StarredGroupElabError (CheckedStarredGroupSource model) :=
  match hModel : model.validate with
  | .error error => .error (.resolve error)
  | .ok () =>
      match source.resolveBase declaringGroup with
      | .error error => .error error.toElabError
      | .ok basePath =>
          match model.lookupUniqueRepeatablePath (basePath ++ source.groups.map (·.name)) with
          | .error error => .error (.resolve error)
          | .ok group =>
              if hPopulated : model.groupContributesField group.path = true then
              match elaborateStarPathPlan model basePath source.groups group.path with
              | .error error => .error (.path error)
              | .ok plan =>
                  if hGroup : model.repeatableGroups.contains group = true then
                    if hAncestry : plan.path.axes.map (·.level) =
                        model.repeatableScopeForGroupPath group.path then
                      .ok {
                        declaringGroup
                        group
                        path := plan.path
                        modelWellFormed := by rw [hModel]; rfl
                        groupOwned := hGroup
                        groupPopulated := hPopulated
                        ancestryOwned := hAncestry
                        firstStarWithin := plan.firstStarWithin
                        pathValid := plan.pathValid }
                    else
                      .error .incoherentCore
                  else
                    .error .incoherentCore
              else
                .error (.groupHasNoFields group.path)

/-- Resolve one starred group operand and retain whether its terminal is a structural repeatable row or an ordinary descendant-derived group product. -/
def elaborateStarredGroupOperandSource (model : FlatModel)
    (declaringGroup : GroupPath) (source : SurfaceStarGroupPath) :
    Except StarredGroupElabError (CheckedStarredGroupOperandSource model) :=
  match hModel : model.validate with
  | .error error => .error (.resolve error)
  | .ok () =>
      match source.resolveBase declaringGroup with
      | .error error => .error error.toElabError
      | .ok basePath =>
          let groupPath := basePath ++ source.groups.map (·.name)
          if hRepeatable :
              model.repeatableGroups.any (fun group => group.path == groupPath) = true then
            (elaborateStarredGroupSource model declaringGroup source).map
              .terminalRepeatable
          else if hOwned : model.hasGroupPath groupPath = true then
            match elaborateStarPathPlan model basePath source.groups groupPath with
            | .error error => .error (.path error)
            | .ok plan =>
                if hAncestry : plan.path.axes.map (·.level) =
                    model.repeatableScopeForGroupPath groupPath then
                  .ok (.terminalPresence {
                    declaringGroup
                    groupPath
                    path := plan.path
                    modelWellFormed := by rw [hModel]; rfl
                    groupOwned := hOwned
                    terminalNonrepeatable := by
                      cases hTerminal :
                          model.repeatableGroups.any
                            (fun group => group.path == groupPath) <;>
                        simp_all
                    ancestryOwned := hAncestry
                    firstStarWithin := plan.firstStarWithin
                    pathValid := plan.pathValid })
                else
                  .error .incoherentCore
          else
            .error (.unknownGroup groupPath)

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
  operator.toGroupFillQuantifier.evalTally
    (GroupListPresenceTally.filledOnly count)

namespace CheckedStarredGroupSource

/-- Whether the normalized identifiers for this starred group establish its complete reduced-universal extent in the current rule-iteration row. The group path is deliberately the target, so descendant field identifiers do not project upward into coverage. -/
def allRowsRelevant (checked : CheckedStarredGroupSource model)
    (scope : ValidationRelevanceScope) (outer : Env) : Bool :=
  scope.coversAggregateExtent model checked.group.path
    checked.path.bindingScope checked.path.reopenedScope outer

/-- Recheck the declaring group and model-owned facts carried by one resolved starred group source at a generic checked-core boundary. -/
def wellFormedBool (checked : CheckedStarredGroupSource model)
    (rowGroup : GroupPath) : Bool :=
  checked.declaringGroup == rowGroup && model.validate.isOk &&
    model.repeatableGroups.contains checked.group &&
    model.groupContributesField checked.group.path &&
    checked.path.axes.map (·.level) ==
      model.repeatableScopeForGroupPath checked.group.path &&
    decide (checked.path.firstStar < checked.path.axes.length) &&
    checked.path.validate.isOk

/-- Resolve the canonical nested topology once, retaining its exact terminal-row environments. -/
def resolvedTopology (checked : CheckedStarredGroupSource model)
    (document : Document) (outer : Env) : Except StarAddressingError ResolvedStarTopology :=
  checked.path.resolve document outer

/-- Count concrete terminal repeatable rows without consulting descendant cells. -/
def rowCount (checked : CheckedStarredGroupSource model)
    (document : Document) (outer : Env) : Except StarAddressingError Nat := do
  let resolved ← checked.resolvedTopology document outer
  pure resolved.environments.length

/-- Count only topology rows within every declared repeatability. Numeric starred group counts use this evaluation domain while structural group-presence predicates continue to observe every instantiated row through `rowCount`. -/
def inCapacityRowCount (checked : CheckedStarredGroupSource model)
    (document : Document) (outer : Env) : Except StarAddressingError Nat := do
  let resolved ← checked.resolvedTopology document outer
  pure (resolved.environments.countP fun environment =>
    !StarAxes.environmentOverLimit checked.path.axes environment)

/-- Evaluate either legal sole-star group predicate from the shared structural row count. -/
def evaluateFull (checked : CheckedStarredGroupSource model)
    (operator : StarredGroupFillQuantifier) (document : Document) (outer : Env) :
    Except StarAddressingError ValidationFillOutcome := do
  pure (operator.evalCount (← checked.rowCount document outer))

/-- The sole-star numeric form excludes over-limit rows while retaining them in the structural topology used by group-presence predicates. -/
def numberOfFilledGroups (checked : CheckedStarredGroupSource model)
    (document : Document) (outer : Env) : Except StarAddressingError FilledGroupCount := do
  pure (.value (← checked.inCapacityRowCount document outer))

/-- Compare the structural row count against the terminal group's declared extent when that extent
    is retained by the checked model. A model without a finite retained extent yields `none` rather
    than acquiring an unmeasured movement rule. -/
def numberOfFilledGroupsOperand? (checked : CheckedStarredGroupSource model)
    (document : Document) (outer : Env) :
    Except StarAddressingError (Option NumericOperand) := do
  let count ← checked.numberOfFilledGroups document outer
  pure (checked.group.repeatability.bind fun extent =>
    (count.availableWithFillability? extent).map fun available =>
      .value available.1 available.2)

/-- Count the starred group in partial validation only after its group-path extent is known. The gate precedes topology resolution. -/
def evaluatePartialNumberOfFilledGroups
    (checked : CheckedStarredGroupSource model)
    (document : Document) (outer : Env) (scope : ValidationRelevanceScope) :
    Except StarAddressingError PartialValidationFilledGroupCountResult :=
  if checked.allRowsRelevant scope outer then do
    pure (.evaluated (← checked.numberOfFilledGroups document outer))
  else
    pure .nonRelevant

end CheckedStarredGroupSource

namespace CheckedStarredGroupPresenceSource

/-- Recheck the exact model-owned terminal group and shared topology certificate at a generic checked-core boundary. -/
def wellFormedBool (checked : CheckedStarredGroupPresenceSource model)
    (rowGroup : GroupPath) : Bool :=
  checked.declaringGroup == rowGroup && model.validate.isOk &&
    model.hasGroupPath checked.groupPath &&
    !model.repeatableGroups.any (fun group => group.path == checked.groupPath) &&
    checked.path.axes.map (·.level) ==
      model.repeatableScopeForGroupPath checked.groupPath &&
    decide (checked.path.firstStar < checked.path.axes.length) &&
    checked.path.validate.isOk

/-- Resolve the same canonical nested topology used by every checked starred consumer. -/
def resolvedTopology (checked : CheckedStarredGroupPresenceSource model)
    (document : Document) (outer : Env) :
    Except StarAddressingError ResolvedStarTopology :=
  checked.path.resolve document outer

end CheckedStarredGroupPresenceSource

end A12Kernel
