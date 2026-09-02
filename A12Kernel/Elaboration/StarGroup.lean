import A12Kernel.Elaboration.SingleGroup
import A12Kernel.Elaboration.StarPath
import A12Kernel.Semantics.GroupPresence
import A12Kernel.Semantics.NumericComparison

/-! # Checked group-star consumers

This capsule resolves a starred group path through the shared model-derived topology. A terminal repeatable group retains the established structural-row interpretation used by the two legal group predicates and `NumberOfFilledGroups`, with all three consumers restricted to instantiated in-capacity rows. Partial numeric counting applies the local reduced-universal group-path account that reproduces the measured fifth outcome pattern, while the measured sole-star threshold carrier selects exact relevant in-capacity group rows. A nonrepeatable terminal retains its exact group path so checked full validation can derive the existing descendant-content/error product once per in-capacity topology environment; partial validation of a sole such operand selects the same in-capacity environments and delegates each product to the relevance-aware checked-rule resolver. Mixed or repeated partial lists, filters, computation's ordered scan, and wider whole-rule orchestration remain outside.
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
  one. Only a repeatable group reaches this here, which is not an assumption but a consequence:
  `hasGroupPath_nonrepeatable_contributesField` proves that a present nonrepeatable group carries a
  field, so the nonrepeatable terminal branch cannot reach this arm. -/
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

/-- Select the only two group-list quantifiers whose single starred operand has a measured partial route. -/
def GroupFillQuantifier.toStarredGroupFillQuantifier? :
    GroupFillQuantifier → Option StarredGroupFillQuantifier
  | .noGroupFilled => some .noGroupFilled
  | .atLeastOneGroupFilled => some .atLeastOneGroupFilled
  | .allGroupsFilled | .notAllGroupsFilled
  | .groupsNotCollectivelyFilled => none

/-- Every row supplied by the carrier is structural group content, including a created-but-empty row. Capacity selection belongs to the checked call site. -/
def StarredGroupFillQuantifier.evalCount (operator : StarredGroupFillQuantifier)
    (count : Nat) : ValidationFillOutcome :=
  operator.toGroupFillQuantifier.evalTally
    (GroupListPresenceTally.filledOnly count)

/-- Resolve the shared topology and retain only environments within every declared repeatability. -/
def StarPath.inCapacityEnvironments (path : StarPath)
    (document : Document) (outer : Env) : Except StarAddressingError (List Env) := do
  let resolved ← path.resolve document outer
  pure (resolved.environments.filter fun environment =>
    !StarAxes.environmentOverLimit path.axes environment)

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

/-- Count only topology rows within every declared repeatability. -/
def inCapacityRowCount (checked : CheckedStarredGroupSource model)
    (document : Document) (outer : Env) : Except StarAddressingError Nat := do
  pure (← checked.path.inCapacityEnvironments document outer).length

/-- Select the partial-validation in-capacity row count when the caller either covers the whole
    starred extent or names at least one concrete in-capacity group row. A selection confined to
    over-limit rows is unavailable rather than an empty operand. -/
def partialInCapacityRowCount? (checked : CheckedStarredGroupSource model)
    (document : Document) (outer : Env) (scope : ValidationRelevanceScope) :
    Except StarAddressingError (Option Nat) := do
  let environments ← checked.path.inCapacityEnvironments document outer
  if checked.allRowsRelevant scope outer then
    pure (some environments.length)
  else
    let relevant := environments.filter fun environment =>
      scope.coversCell model checked.group.path environment
    if relevant.isEmpty then pure none else pure (some relevant.length)

/-- Evaluate either legal sole-star group predicate from the instantiated in-capacity row count. -/
def evaluateFull (checked : CheckedStarredGroupSource model)
    (operator : StarredGroupFillQuantifier) (document : Document) (outer : Env) :
    Except StarAddressingError ValidationFillOutcome := do
  pure (operator.evalCount (← checked.inCapacityRowCount document outer))

/-- Evaluate the measured single-star partial carrier without treating an unavailable selected
    extent as zero rows. -/
def evaluatePartialQuantifier (checked : CheckedStarredGroupSource model)
    (operator : StarredGroupFillQuantifier) (document : Document) (outer : Env)
    (scope : ValidationRelevanceScope) : Except StarAddressingError Verdict := do
  match ← checked.partialInCapacityRowCount? document outer scope with
  | some count => pure (operator.evalCount count).asConservativeVerdict
  | none => pure .unknown

/-- The sole-star numeric form counts the same instantiated in-capacity rows as the threshold predicates. -/
def numberOfFilledGroups (checked : CheckedStarredGroupSource model)
    (document : Document) (outer : Env) : Except StarAddressingError FilledGroupCount := do
  pure (.value (← checked.inCapacityRowCount document outer))

/-- Compare the in-capacity structural row count against the terminal group's declared extent when that extent
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

/-- Resolve a nonrepeatable group terminal only at in-capacity environments of its starred ancestry. -/
def inCapacityEnvironments (checked : CheckedStarredGroupPresenceSource model)
    (document : Document) (outer : Env) : Except StarAddressingError (List Env) :=
  checked.path.inCapacityEnvironments document outer

end CheckedStarredGroupPresenceSource

/-- Re-spell an ordinary group path as a star plan whose **terminal** group carries the wildcard,
    which is the only starred group-operand shape measured for this operator. A path navigating by
    parent count has no representation as a star plan, so it is refused rather than approximated. -/
def SurfaceGroupPath.toTerminalStarred (path : SurfaceGroupPath) :
    Option SurfaceStarGroupPath :=
  if path.turningPoint.isSome then none
  else
    match path.groups.reverse with
    | [] => none
    | terminal :: reversedPrefix =>
        some { base := path.base
               groups := reversedPrefix.reverse.map (fun name => { name }) ++
                 [{ name := terminal, starred := true }] }

/-- One checked operand of a filled-group count, in the carrier that admits both forms in one list.

    The two contribute unlike quantities into the **same** result domain — an indicator for a fixed
    operand, a cardinality for a starred one — so a consumer folds them in one traversal with a
    form-dependent contribution rather than carrying a result type per form. `GroupCountOperandReading`
    owns that fold; this type is only its checked input.

    A starred operand keeps its full `CheckedStarredGroupSource` rather than a resolved path, because
    the quantity it contributes is the in-capacity instantiated row count and that needs the star
    plan's topology. It is the same certificate the starred validation carriers already consume. -/
inductive CheckedGroupCountOperand (model : FlatModel) where
  | fixed (reference : ResolvedGroupReference)
  | starred (source : CheckedStarredGroupSource model)

namespace CheckedGroupCountOperand

/-- Whether the operand's group subtree contains the computed target, which is the self-reference
    gate every group-valued operand shares. -/
def referencesField (operand : CheckedGroupCountOperand model)
    (model' : FlatModel) (field : FieldId) : Bool :=
  match operand with
  | .fixed reference => reference.referencesField model' field
  | .starred source =>
      match model'.lookupUniqueId field with
      | .ok declaration => source.group.path.isPrefixOf declaration.groupPath
      | .error _ => false


/-- Whether the operand names a root group, which every group-count carrier refuses. A starred
    operand's own group path carries the same rule as a fixed reference's. -/
def isRoot (operand : CheckedGroupCountOperand model) : Bool :=
  match operand with
  | .fixed reference => reference.isRoot
  | .starred source => source.group.path.length == 1

/-- The operand's contribution to the count's declared extent: one slot for a fixed group, and the
    declared row maximum for a starred one. `none` leaves the whole count without a finite extent to
    reach rather than acquiring an unmeasured movement rule; `RepeatableGroupDecl.repeatability`
    owns why no authorable model selects that branch. -/
def declaredExtent? (operand : CheckedGroupCountOperand model) : Option Nat :=
  match operand with
  | .fixed _ => some 1
  | .starred source => source.group.repeatability


/-- The group this operand counts over, whichever form it takes. -/
def groupPath (operand : CheckedGroupCountOperand model) : GroupPath :=
  match operand with
  | .fixed reference => reference.path
  | .starred source => source.group.path

/-- Whether two operands duplicate one another. Containment either way is a duplicate however each
    side is spelled, and equal paths are a duplicate too — except when **both** are starred, which
    the Kernel admits and counts once per position rather than once per group
    ([checkpoint](../../docs/SOURCES.md#src-group-count-list-extent)). That exception is what makes
    this a containment rule rather than a distinctness rule, and it is measured rather than derived
    from the fixed-only carrier it generalizes. -/
def duplicates (left right : CheckedGroupCountOperand model) : Bool :=
  if left.groupPath == right.groupPath then
    match left, right with
    | .starred _, .starred _ => false
    | _, _ => true
  else
    left.groupPath.isPrefixOf right.groupPath ||
      right.groupPath.isPrefixOf left.groupPath

/-- The first duplicate pair in authored order, reported as the two group paths the refusal names.
    Equal paths select the Kernel's own equal-operand class and containment its containment class,
    so the caller needs no second scan to tell them apart. -/
def firstDuplicate? : List (CheckedGroupCountOperand model) →
    Option (GroupPath × GroupPath)
  | [] => none
  | first :: rest =>
      match rest.find? (first.duplicates ·) with
      | some other => some (first.groupPath, other.groupPath)
      | none => firstDuplicate? rest

end CheckedGroupCountOperand

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

/-- A starred group operand resolves only against a representable declaring group.

    Stated here rather than in a proof module because the guard it reads sits in
    `SurfaceStarGroupPath.resolveBase`, which is private construction detail: exporting that
    definition to state the lemma elsewhere would expose the base walk for no consumer. Every other
    operand kind's guard is already public, so this is the one arm that needs a local statement. -/
theorem elaborateStarredGroupOperandSource_declaringGroupValid
    {model : FlatModel} {declaringGroup : GroupPath} {source : SurfaceStarGroupPath}
    {checked : CheckedStarredGroupOperandSource model}
    (resolved :
      elaborateStarredGroupOperandSource model declaringGroup source = .ok checked) :
    GroupPath.isValid declaringGroup = true := by
  cases hValid : GroupPath.isValid declaringGroup with
  | true => rfl
  | false =>
    rw [elaborateStarredGroupOperandSource] at resolved
    split at resolved
    · cases resolved
    · rw [SurfaceStarGroupPath.resolveBase] at resolved
      simp only [hValid, Bool.not_false, if_true, bind, Except.bind, throw, throwThe,
        MonadExceptOf.throw] at resolved
      cases resolved

end A12Kernel
