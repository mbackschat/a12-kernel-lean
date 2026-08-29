import A12Kernel.Elaboration.Flat.Context
import A12Kernel.Semantics.GroupPresence
import A12Kernel.Semantics.StarAddressing

/-! # Checked general star-path lowering

This boundary resolves structured group-segment stars against one validated `FlatModel`, derives the exact outer-to-inner repeatable axes from the field declaration, and identifies the first reopened axis. Runtime rows remain owned by `StarAddressing`.
-/

namespace A12Kernel

/-- One decoded group-path segment with its authored wildcard marker. -/
structure SurfaceStarGroupSegment where
  name : String
  starred : Bool := false
  deriving Repr, DecidableEq

/-- A decoded field path whose group segments retain their individual wildcard markers. Parent navigation itself is never wildcardable. -/
structure SurfaceStarFieldPath where
  base : PathBase
  /-- Optional explicit name of the parent-walk turning point. -/
  turningPoint : Option String := none
  groups : List SurfaceStarGroupSegment
  field : String
  deriving Repr, DecidableEq

/-- One path-segment selector from the partial-validation relevant-entity set. `all` is the public wildcard; a concrete selector cannot establish all-rows knowledge at a repeatable level. -/
inductive RelevanceIndex where
  | all
  | concrete (index : Nat)
  deriving Repr, DecidableEq

/-- One already-decoded partial-validation relevant entity. Its index vector is aligned with every path segment, including nonrepeatable groups and the terminal field. -/
structure RelevantEntityPattern where
  path : List String
  indices : List RelevanceIndex
  deriving Repr, DecidableEq

/-- Full validation has complete relevance by definition; partial validation retains the caller's wildcardable entity patterns. -/
inductive ValidationRelevanceScope where
  | full
  | partialSet (entities : List RelevantEntityPattern)
  deriving Repr, DecidableEq

namespace SurfaceStarFieldPath

def toFieldPath (source : SurfaceStarFieldPath) : SurfaceFieldPath :=
  { base := source.base
    turningPoint := source.turningPoint
    groups := source.groups.map (·.name)
    field := source.field }

end SurfaceStarFieldPath

namespace RelevantEntityPattern

/-- The all-instances partial-validation pattern for one model path. Every path segment receives the public wildcard, including nonrepeatable segments where it is observationally inert. -/
def allInstances (path : List String) : RelevantEntityPattern :=
  { path, indices := path.map fun _ => .all }

private def actualIndex? (model : FlatModel) (environment : Env)
    (path : GroupPath) : Option Nat :=
  match model.repeatableGroups.find? fun group => group.path == path with
  | none => some 1
  | some group =>
      (environment.bindingAt group.level).toOption

private def cellPrefixMatches (model : FlatModel) (environment : Env) :
    GroupPath → List String → List RelevanceIndex → Bool
  | _, [], [] => true
  | pathPrefix, segment :: segments, index :: indices =>
      let path := pathPrefix ++ [segment]
      match actualIndex? model environment path with
      | none => false
      | some actual =>
          let currentMatches := match index with
            | .all => true
            | .concrete expected => expected == actual
          currentMatches && cellPrefixMatches model environment path segments indices
  | _, _, _ => false

/-- Expand one target path's relevant identifier. An ancestor contributes the target while retaining its own coordinates and wildcarding every deeper segment. A descendant never projects upward, and malformed index arity never becomes coverage. -/
def projectOntoTarget? (entity : RelevantEntityPattern)
    (targetPath : List String) : Option RelevantEntityPattern :=
  if entity.indices.length != entity.path.length ||
      !entity.path.isPrefixOf targetPath then
    none
  else
    some {
      path := targetPath
      indices := entity.indices ++
        (targetPath.drop entity.path.length).map fun _ => .all
    }

private def indexVectorEncompasses :
    List RelevanceIndex → List RelevanceIndex → Bool
  | [], [] => true
  | .all :: broad, _ :: narrow => indexVectorEncompasses broad narrow
  | .concrete expected :: broad, .concrete actual :: narrow =>
      expected == actual && indexVectorEncompasses broad narrow
  | _, _ => false

/-- Whether this normalized identifier is at least as broad as another identifier for the same field. -/
def encompasses (broad narrow : RelevantEntityPattern) : Bool :=
  broad.path == narrow.path &&
    indexVectorEncompasses broad.indices narrow.indices

private def matchesBoundSubtreeAt (entity : RelevantEntityPattern)
    (model : FlatModel) (boundLevels : List RepeatableLevel)
    (outer : Env) : GroupPath → List String → List RelevanceIndex → Bool
  | _, [], [] => true
  | pathPrefix, segment :: segments, index :: indices =>
      let path := pathPrefix ++ [segment]
      let matchesHere :=
        match model.repeatableGroups.find? fun group => group.path == path with
        | some group =>
            if boundLevels.contains group.level then
              match (outer.bindingAt group.level).toOption with
              | some actual => index == .all || index == .concrete actual
              | none => false
            else
              true
        | none => true
      matchesHere &&
        matchesBoundSubtreeAt entity model boundLevels outer path segments indices
  | _, _, _ => false

/-- Whether one normalized target identifier can belong to the current rule-iteration subtree. Concrete disagreement at a level above the first star removes it; wildcard or exact agreement retains it. -/
def matchesBoundSubtree (entity : RelevantEntityPattern)
    (model : FlatModel) (boundLevels : List RepeatableLevel)
    (outer : Env) : Bool :=
  matchesBoundSubtreeAt entity model boundLevels outer []
    entity.path entity.indices

private def wildcardsLevelsAt (entity : RelevantEntityPattern)
    (model : FlatModel) (levels : List RepeatableLevel) :
    GroupPath → List String → List RelevanceIndex → Bool
  | _, [], [] => true
  | pathPrefix, segment :: segments, index :: indices =>
      let path := pathPrefix ++ [segment]
      let wildcardHere :=
        match model.repeatableGroups.find? fun group => group.path == path with
        | some group => !levels.contains group.level || index == .all
        | none => true
      wildcardHere && wildcardsLevelsAt entity model levels path segments indices
  | _, _, _ => false

/-- Whether one normalized target identifier wildcards every repeatable level reopened by the operand's first star. -/
def wildcardsLevels (entity : RelevantEntityPattern)
    (model : FlatModel) (levels : List RepeatableLevel) : Bool :=
  wildcardsLevelsAt entity model levels [] entity.path entity.indices

/-- Project one caller identifier onto the operand field and test the starred value-list's existential extent gate in the current iteration subtree. -/
def coversValueListExtent (entity : RelevantEntityPattern)
    (model : FlatModel) (targetPath : List String)
    (boundLevels reopenedLevels : List RepeatableLevel) (outer : Env) : Bool :=
  match entity.projectOntoTarget? targetPath with
  | none => false
  | some projected =>
      projected.matchesBoundSubtree model boundLevels outer &&
        projected.wildcardsLevels model reopenedLevels

/-- Remove exact duplicates and every narrower target identifier encompassed by another retained wildcard identifier. -/
def reduceWildcardDominance (entities : List RelevantEntityPattern) :
    List RelevantEntityPattern :=
  let unique := entities.eraseDups
  unique.filter fun entity =>
    !unique.any fun broader => broader != entity && broader.encompasses entity

/-- Whether this one entity covers a concrete target instance. Exact fields and ancestor groups share the same prefix/index rule; wildcard indices match any concrete coordinate. -/
def coversCell (entity : RelevantEntityPattern) (model : FlatModel)
    (targetPath : List String) (environment : Env) : Bool :=
  entity.path.isPrefixOf targetPath &&
    cellPrefixMatches model environment [] entity.path entity.indices

/-- Whether one selected entity intersects a concrete group instance. An ancestor selection covers the group; a descendant selection contributes partial coverage when its shared repetition prefix identifies the same instance. -/
def touchesGroup (entity : RelevantEntityPattern) (model : FlatModel)
    (groupPath : GroupPath) (environment : Env) : Bool :=
  if entity.path.isPrefixOf groupPath then
    entity.coversCell model groupPath environment
  else if groupPath.isPrefixOf entity.path then
    ({ path := groupPath
       indices := entity.indices.take groupPath.length } :
      RelevantEntityPattern).coversCell model groupPath environment
  else
    false

private def coversDescendantCompletely
    (entity : RelevantEntityPattern) (model : FlatModel)
    (groupPath : GroupPath) (environment : Env)
    (fieldPath : List String) : Bool :=
  entity.touchesGroup model groupPath environment &&
    entity.path.isPrefixOf fieldPath &&
    model.repeatableGroups.all fun group =>
      if groupPath.length < group.path.length &&
          group.path.isPrefixOf entity.path then
        entity.indices[group.path.length - 1]? ==
          some RelevanceIndex.all
      else
        true

end RelevantEntityPattern

namespace ValidationRelevanceScope

/-- Add every model-owned global field to a partial-validation call at the common scope boundary. Full validation is already complete. -/
def withGlobals (scope : ValidationRelevanceScope)
    (model : FlatModel) : ValidationRelevanceScope :=
  match scope with
  | .full => .full
  | .partialSet entities =>
      .partialSet (entities ++
        (model.fields.filter (·.isGlobal)).map fun declaration =>
          RelevantEntityPattern.allInstances declaration.path)

/-- Prepare one all-rows operand's target-specific identifier set: expand ancestors, retain the current iteration subtree, then remove wildcard-dominated siblings. -/
def aggregateExtentPatterns (entities : List RelevantEntityPattern)
    (model : FlatModel) (targetPath : List String)
    (boundLevels : List RepeatableLevel) (outer : Env) :
    List RelevantEntityPattern :=
  ((entities.filterMap fun entity => entity.projectOntoTarget? targetPath).filter
    fun entity => entity.matchesBoundSubtree model boundLevels outer)
    |> RelevantEntityPattern.reduceWildcardDominance

/-- All-rows aggregate relevance is universal over the normalized retained identifiers. The set must be nonempty, and every identifier must wildcard every level reopened from the first star. -/
def coversAggregateExtent (scope : ValidationRelevanceScope) (model : FlatModel)
    (targetPath : List String) (boundLevels reopenedLevels : List RepeatableLevel)
    (outer : Env) : Bool :=
  match scope with
  | .full => true
  | .partialSet entities =>
      let retained := aggregateExtentPatterns entities model targetPath boundLevels outer
      !retained.isEmpty &&
        retained.all fun entity => entity.wildcardsLevels model reopenedLevels

/-- A starred value-list entry uses its separate existential covering-identifier gate. Concrete siblings do not cancel a qualifying wildcard. -/
def coversValueListExtent (scope : ValidationRelevanceScope) (model : FlatModel)
    (targetPath : List String) (boundLevels reopenedLevels : List RepeatableLevel)
    (outer : Env) : Bool :=
  match scope with
  | .full => true
  | .partialSet entities => entities.any fun entity =>
      entity.coversValueListExtent model targetPath boundLevels reopenedLevels outer

/-- Per-cell relevance retains concrete row identity and ancestor descent. Unlike all-rows relevance, different concrete entities may cover different reached cells. -/
def coversCell (scope : ValidationRelevanceScope) (model : FlatModel)
    (targetPath : List String) (environment : Env) : Bool :=
  match scope with
  | .full => true
  | .partialSet entities =>
      entities.any fun entity => entity.coversCell model targetPath environment

/-- Resolve a field ID through the checked model before applying per-instance relevance. An unresolved or ambiguous ID cannot become relevant. -/
def coversField (scope : ValidationRelevanceScope) (model : FlatModel)
    (field : FieldId) (environment : Env) : Bool :=
  match model.lookupUniqueId field with
  | .ok declaration => scope.coversCell model declaration.path environment
  | .error _ => false

/-- Resolve the partial rule-run gate at exactly the repeatable levels bound by the rule's checked iteration plan. A relevant field or ancestor must still project onto the error path, coordinates at bound levels must match the current environment, and deeper coordinates are deliberately ignored because iteration did not choose them. This is distinct from exact per-cell relevance used by condition leaves. -/
def coversFieldAtBoundLevels (scope : ValidationRelevanceScope)
    (model : FlatModel) (field : FieldId)
    (boundLevels : List RepeatableLevel) (environment : Env) : Bool :=
  match model.lookupUniqueId field with
  | .error _ => false
  | .ok declaration =>
      match scope with
      | .full => true
      | .partialSet entities => entities.any fun entity =>
          match entity.projectOntoTarget? declaration.path with
          | none => false
          | some projected =>
              projected.matchesBoundSubtree model boundLevels environment

/-- Derive the kernel's three-level relevance for one concrete group instance. Any intersecting selection supplies partial visibility; definite absence additionally requires an ancestor group selection or complete coverage of every declared descendant, wildcarded across every deeper repeatable level. -/
def groupRelevance (scope : ValidationRelevanceScope) (model : FlatModel)
    (groupPath : GroupPath) (environment : Env) : GroupRelevance :=
  match scope with
  | .full => .fullyRelevant
  | .partialSet entities =>
      if !entities.any fun entity =>
          entity.touchesGroup model groupPath environment then
        .noneRelevant
      else if entities.any fun entity =>
          entity.coversCell model groupPath environment then
        .fullyRelevant
      else if (model.fields.filter fun declaration =>
          groupPath.isPrefixOf declaration.groupPath).all fun declaration =>
          entities.any fun entity =>
            entity.coversDescendantCompletely model groupPath environment
              declaration.path then
        .fullyRelevant
      else
        .partlyRelevant

end ValidationRelevanceScope

inductive StarPathElabError where
  | resolve (error : ResolveError)
  | wildcardOnNonrepeatable (path : GroupPath)
  | missingWildcard (path : List String)
  | iterationBelowWildcard (path : GroupPath)
  | addressing (error : StarAddressingError)
  | incoherentCore
  deriving Repr, DecidableEq

/-- One field declaration and general star plan certified against the same validated model. -/
structure CheckedStarFieldPath (model : FlatModel) where
  declaration : FlatFieldDecl
  path : StarPath
  modelWellFormed : model.validate.isOk = true
  declarationOwned : model.fields.contains declaration = true
  ancestryOwned : path.axes.map (·.level) = declaration.repeatableScope
  firstStarWithin : path.firstStar < path.axes.length
  pathValid : path.validate.isOk = true

/-- A model-derived star plan with the structural obligations required by every checked field or group consumer. -/
structure CheckedStarPlan where
  path : StarPath
  firstStarWithin : path.firstStar < path.axes.length
  pathValid : path.validate.isOk = true

/-- Whether one topology-produced concrete field instance is relevant to this validation call. -/
def CheckedStarFieldPath.cellRelevant (checked : CheckedStarFieldPath model)
    (scope : ValidationRelevanceScope) (environment : Env) : Bool :=
  scope.coversCell model checked.declaration.path environment

namespace CheckedStarFieldPath

/-- Repeatable levels strictly above the first star remain fixed by the surrounding rule environment. The starred level and every deeper axis stay operand-local. -/
def bindingScope (checked : CheckedStarFieldPath model) :
    List RepeatableLevel :=
  checked.path.bindingScope

/-- Repeatable levels reopened by this operand, beginning at its first star. -/
def reopenedScope (checked : CheckedStarFieldPath model) :
    List RepeatableLevel :=
  checked.path.reopenedScope

/-- Whether this checked starred field is completely relevant for an all-rows aggregate in the current rule-iteration row. -/
def allRowsRelevant (checked : CheckedStarFieldPath model)
    (scope : ValidationRelevanceScope) (outer : Env) : Bool :=
  scope.coversAggregateExtent model checked.declaration.path
    checked.bindingScope checked.reopenedScope outer

/-- Whether this checked starred field has one covering wildcard identifier for a value-list extent in the current rule-iteration row. -/
def valueListExtentRelevant (checked : CheckedStarFieldPath model)
    (scope : ValidationRelevanceScope) (outer : Env) : Bool :=
  scope.coversValueListExtent model checked.declaration.path
    checked.bindingScope checked.reopenedScope outer

/-- Whether one topology-produced leaf environment lies under any over-capacity repeatable ancestor. This structural check is independent of the terminal field kind. -/
def environmentOverLimit (checked : CheckedStarFieldPath model)
    (environment : Env) : Bool :=
  StarAxes.environmentOverLimit checked.path.axes environment

/-- Overlay the path-owned over-repetition finding on an already checked cell. This is the common seam for raw-validation readers and future checked-document consumers. -/
def contextualizeCell (checked : CheckedStarFieldPath model)
    (environment : Env) (scalar : CheckedCell) : CheckedCell :=
  scalar.withOverRepetitionIf (checked.environmentOverLimit environment)

/-- Apply the declaration-owned scalar checker and then the shared structural overlay. Every raw typed-star consumer shares this checked-cell boundary. -/
def checkedCell (checked : CheckedStarFieldPath model)
    (read : Env → FieldId → RawCell) (environment : Env) : CheckedCell :=
  checked.contextualizeCell environment
    (checked.declaration.checkRaw (read environment checked.declaration.id))

/-- Classify a declaration-certified String leaf through the common normalized token reader. This is shared by starred value lists and heterogeneous repetition keys. -/
def stringValueListCell (checked : CheckedStarFieldPath model)
    (field : FlatStringField)
    (fieldOwned : checked.declaration.toStringValueField? = some field)
    (read : Env → FieldId → RawCell) (environment : Env) : ValueListCell .token :=
  match hField : checked.declaration.toStringValueField? with
  | some resolved =>
    if hOwned : resolved = field then
    let context : FlatContext := {
      read := fun id =>
        if id == field.id then checked.checkedCell read environment
        else malformedCheckedCell }
    (FlatTextFieldOperand.string field).valueListCell context
    else False.elim (by simp_all)
  | none => False.elim (by simp_all)

/-- Resolve canonical topology once and classify every leaf in its established order. -/
def resolvedValueListSide (checked : CheckedStarFieldPath model)
    (document : Document) (outer : Env) (classify : Env → ValueListCell kind) :
    Except StarAddressingError (ResolvedValueListSide kind) := do
  let resolved ← checked.path.resolve document outer
  pure (resolved.toResolvedSide classify)

/-- Retain only relevant concrete cells before invoking the kind-specific classifier, while recording whether the star's complete extent is wildcard-covered. Concrete enumeration of every current row does not establish that future/absent rows are relevant. -/
def selectedPartialValueListSide (checked : CheckedStarFieldPath model)
    (resolved : ResolvedStarTopology) (outer : Env)
    (scope : ValidationRelevanceScope)
    (classify : Env → ValueListCell kind) :
    ResolvedValueListQuantifierSide kind :=
  let relevant := resolved.environments.filter fun environment =>
    checked.cellRelevant scope environment
  { side := {
      cells := relevant.map classify
      hasUninstantiatedTail := resolved.domain.hasOpenTail
      hasHaving := false }
    hasNonRelevant := !checked.valueListExtentRelevant scope outer }

/-- Resolve canonical topology once, then apply per-cell relevance before kind-specific classification. -/
def resolvedPartialValueListSide (checked : CheckedStarFieldPath model)
    (document : Document) (outer : Env) (scope : ValidationRelevanceScope)
    (classify : Env → ValueListCell kind) :
    Except StarAddressingError (ResolvedValueListQuantifierSide kind) := do
  let resolved ← checked.path.resolve document outer
  pure (checked.selectedPartialValueListSide resolved outer scope classify)

end CheckedStarFieldPath

private structure MarkedStarAxis where
  path : GroupPath
  axis : StarAxis
  starred : Bool

private def firstInvalidWildcard? (model : FlatModel) :
    GroupPath → List SurfaceStarGroupSegment → Option GroupPath
  | _, [] => none
  | pathPrefix, segment :: rest =>
      let path := pathPrefix ++ [segment.name]
      if segment.starred &&
          !model.repeatableGroups.any (fun group => group.path == path) then
        some path
      else
        firstInvalidWildcard? model path rest

private def markedAxes (model : FlatModel) :
    GroupPath → List SurfaceStarGroupSegment → List MarkedStarAxis
  | _, [] => []
  | pathPrefix, segment :: rest =>
      let path := pathPrefix ++ [segment.name]
      let tail := markedAxes model path rest
      match model.repeatableGroups.find? (fun group => group.path == path) with
      | none => tail
      | some group =>
          { path
            axis := { level := group.level, repeatability := group.repeatability }
            starred := segment.starred } :: tail

private def firstStarredAxis? : List MarkedStarAxis → Nat → Option Nat
  | [], _ => none
  | axis :: rest, index =>
      if axis.starred then some index else firstStarredAxis? rest (index + 1)

private def firstUnstarredAxis? : List MarkedStarAxis → Option GroupPath
  | [] => none
  | axis :: rest => if axis.starred then firstUnstarredAxis? rest else some axis.path

/-- Select the first reopened axis and validate the resulting plan over already-marked axes.
    Kept separate from wildcard legality so its star-position and validation obligations are
    stated over exactly the axes that were scanned. -/
private def planFromMarkedAxes (marked : List MarkedStarAxis)
    (targetPath : List String) : Except StarPathElabError CheckedStarPlan :=
  -- Explicit matches rather than `do`: the star-position branch below must remain
  -- inspectable so its unreachability can be proved instead of re-checked.
  match firstStarredAxis? marked 0 with
  | none => .error (.missingWildcard targetPath)
  | some firstStar =>
      match firstUnstarredAxis? (marked.drop firstStar) with
      | some path => .error (.iterationBelowWildcard path)
      | none =>
          let path : StarPath := { axes := marked.map (·.axis), firstStar }
          if hFirstStar : path.firstStar < path.axes.length then
            match hPath : path.validate with
            | .error error => .error (.addressing error)
            | .ok () => .ok {
                path
                firstStarWithin := hFirstStar
                pathValid := by rw [hPath]; rfl }
          else
            .error .incoherentCore

/-- Derive the one shared checked star plan after the caller has resolved the terminal field or group. A relative base is supplied separately so its named repeatable ancestors remain fixed before the first authored star. -/
def elaborateStarPathPlan (model : FlatModel) (basePath : GroupPath)
    (groups : List SurfaceStarGroupSegment) (targetPath : List String) :
    Except StarPathElabError CheckedStarPlan :=
  match firstInvalidWildcard? model basePath groups with
  | some path => .error (.wildcardOnNonrepeatable path)
  | none =>
      let baseSegments := basePath.map fun name => ({ name } : SurfaceStarGroupSegment)
      planFromMarkedAxes (markedAxes model [] (baseSegments ++ groups)) targetPath

/-- The recursive prefix walk visits exactly the proper nonempty prefixes that
    `repeatableScopeForGroupPath` indexes, so the marked axes carry the model-derived
    ancestry by construction rather than by a later re-check. -/
private theorem markedAxes_levels (model : FlatModel) :
    ∀ (segments : List SurfaceStarGroupSegment) (prefixPath : GroupPath),
      (markedAxes model prefixPath segments).map (fun marked => marked.axis.level) =
        (List.range segments.length).filterMap fun offset =>
          (model.repeatableGroups.find? fun group =>
            group.path == prefixPath ++ (segments.map (·.name)).take (offset + 1)).map
              (·.level) := by
  intro segments
  induction segments with
  | nil => intro prefixPath; simp [markedAxes]
  | cons segment rest ih =>
      intro prefixPath
      have tail :
          (List.range rest.length).filterMap
              (fun offset =>
                (model.repeatableGroups.find? fun group =>
                  group.path == prefixPath ++
                    ((segment :: rest).map (·.name)).take (offset + 1 + 1)).map (·.level)) =
            (markedAxes model (prefixPath ++ [segment.name]) rest).map
              (fun marked => marked.axis.level) := by
        rw [ih (prefixPath ++ [segment.name])]
        simp [List.append_assoc]
      simp only [markedAxes, List.length_cons, List.range_succ_eq_map, List.map_cons,
        List.filterMap_cons, List.filterMap_map, List.take_succ_cons, List.take_zero,
        Function.comp_def]
      cases hFound : model.repeatableGroups.find? (fun group =>
          group.path == prefixPath ++ [segment.name]) with
      | none => simpa [hFound] using tail.symm
      | some group => simpa [hFound] using tail.symm

/-- The starred-axis scan reports an index inside the axes it scanned. This is the fact the
    planner's own defensive branch re-checks. -/
private theorem firstStarredAxis?_lt :
    ∀ (axes : List MarkedStarAxis) (start index : Nat),
      firstStarredAxis? axes start = some index → index < start + axes.length := by
  intro axes
  induction axes with
  | nil => intro start index found; simp [firstStarredAxis?] at found
  | cons axis rest ih =>
      intro start index found
      simp only [firstStarredAxis?] at found
      simp only [List.length_cons]
      split at found
      · have : index = start := by simpa using found.symm
        subst this
        omega
      · have bound := ih (start + 1) index found
        omega

/-- The extracted plan step never reaches its defensive incoherent-core branch: the scan that
    produced the first starred index already bounds it by the axes it scanned. -/
private theorem planFromMarkedAxes_never_incoherentCore
    (marked : List MarkedStarAxis) (targetPath : List String) :
    planFromMarkedAxes marked targetPath ≠ .error .incoherentCore := by
  unfold planFromMarkedAxes
  cases hStar : firstStarredAxis? marked 0 with
  | none => simp
  | some index =>
      have bound : index < (marked.map (·.axis)).length := by
        simpa using firstStarredAxis?_lt marked 0 index hStar
      cases hBelow : firstUnstarredAxis? (marked.drop index) with
      | some path => simp [hBelow]
      | none =>
          simp only [hBelow, dif_pos bound]
          split <;> simp

/-- A successful plan's axes are exactly the marked axes it scanned. -/
private theorem planFromMarkedAxes_axes (marked : List MarkedStarAxis)
    (targetPath : List String) (plan : CheckedStarPlan)
    (success : planFromMarkedAxes marked targetPath = .ok plan) :
    plan.path.axes = marked.map (·.axis) := by
  unfold planFromMarkedAxes at success
  cases hStar : firstStarredAxis? marked 0 with
  | none => simp [hStar] at success
  | some index =>
      cases hBelow : firstUnstarredAxis? (marked.drop index) with
      | some path => simp [hStar, hBelow] at success
      | none =>
          simp only [hStar, hBelow] at success
          split at success
          · split at success
            · simp at success
            · injection success with plan_eq
              subst plan_eq
              rfl
          · simp at success

/-- A successful plan's axes already equal the model-derived repeatable ancestry of the
    resolved group path. This is what makes each caller's defensive ancestry re-check a dead
    branch instead of a real diagnostic. -/
theorem elaborateStarPathPlan_ancestry (model : FlatModel) (basePath : GroupPath)
    (groups : List SurfaceStarGroupSegment) (targetPath : List String)
    (plan : CheckedStarPlan)
    (success : elaborateStarPathPlan model basePath groups targetPath = .ok plan) :
    plan.path.axes.map (·.level) =
      model.repeatableScopeForGroupPath (basePath ++ groups.map (·.name)) := by
  unfold elaborateStarPathPlan at success
  cases hWildcard : firstInvalidWildcard? model basePath groups with
  | some path => simp [hWildcard] at success
  | none =>
      simp only [hWildcard] at success
      rw [planFromMarkedAxes_axes _ _ _ success, List.map_map]
      simpa [FlatModel.repeatableScopeForGroupPath, List.map_append, List.map_map,
        Function.comp_def] using
        markedAxes_levels model
          (basePath.map (fun name => ({ name } : SurfaceStarGroupSegment)) ++ groups) []

/-- The planner's own defensive incoherent-core branch is unreachable: the first starred axis
    is found by scanning the marked axes, so its index is always inside them. -/
theorem elaborateStarPathPlan_never_incoherentCore (model : FlatModel)
    (basePath : GroupPath) (groups : List SurfaceStarGroupSegment)
    (targetPath : List String) :
    elaborateStarPathPlan model basePath groups targetPath ≠ .error .incoherentCore := by
  unfold elaborateStarPathPlan
  cases hWildcard : firstInvalidWildcard? model basePath groups with
  | some path => simp
  | none =>
      simpa using
        planFromMarkedAxes_never_incoherentCore
          (markedAxes model []
            (basePath.map (fun name => ({ name } : SurfaceStarGroupSegment)) ++ groups))
          targetPath

/-- Resolve a legal starred field path into the exact model-owned ancestry consumed by `StarAddressing`. A relative turning point may precede later stars; the first star and every deeper repeatable level must be explicitly starred. -/
def elaborateStarFieldPath (model : FlatModel) (declaringGroup : GroupPath)
    (source : SurfaceStarFieldPath) :
    Except StarPathElabError (CheckedStarFieldPath model) :=
  match hModel : model.validate with
  | .error error => .error (.resolve error)
  | .ok () => do
      let declaration ←
        model.resolveFieldDeclarationUnchecked declaringGroup source.toFieldPath |>.mapError .resolve
      let basePath ← match source.base with
        | .absolute => pure []
        | .relative parents => GroupPath.walkUp declaringGroup parents |>.mapError .resolve
      let plan ← elaborateStarPathPlan model basePath source.groups declaration.path
      if hDeclaration : model.fields.contains declaration = true then
        if hAncestry : plan.path.axes.map (·.level) = declaration.repeatableScope then
          pure {
            declaration
            path := plan.path
            modelWellFormed := by rw [hModel]; rfl
            declarationOwned := hDeclaration
            ancestryOwned := hAncestry
            firstStarWithin := plan.firstStarWithin
            pathValid := plan.pathValid
          }
        else
          throw .incoherentCore
      else
        throw .incoherentCore

/-- A checked star field path certifies its declaring group. Resolution runs first and rejects an
unrepresentable group, so the five fixed-target star families can state group validity in their own
certificates without re-testing it. -/
theorem elaborateStarFieldPath_declaringGroupValid
    {model : FlatModel} {declaringGroup : GroupPath} {source : SurfaceStarFieldPath}
    {checked : CheckedStarFieldPath model}
    (elaborated : elaborateStarFieldPath model declaringGroup source = .ok checked) :
    GroupPath.isValid declaringGroup = true := by
  unfold elaborateStarFieldPath at elaborated
  split at elaborated
  · cases elaborated
  · cases hResolved :
      model.resolveFieldDeclarationUnchecked declaringGroup source.toFieldPath with
    | error _ =>
        simp only [hResolved, bind, Except.bind, Except.mapError] at elaborated
        cases elaborated
    | ok declaration =>
        exact FlatModel.resolveFieldDeclarationUnchecked_declaringGroupValid hResolved

end A12Kernel
