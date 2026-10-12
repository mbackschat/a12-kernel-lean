import A12Kernel.Elaboration.Flat.Context
import A12Kernel.Semantics.GroupPresence
import A12Kernel.Semantics.StarAddressing

namespace A12Kernel

/-- One path-segment selector from the partial-validation relevant-entity set. `all` is the public wildcard; `concrete` selects one coordinate. Each consumer defines how several selectors combine into extent coverage. -/
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

/-- Cut one identifier below `groupPath` back to that group's depth, keeping its coordinates there.
    An identifier at or above the group is `projectOntoTarget?`'s, and malformed index arity never
    becomes coverage. -/
def cutBackTo? (entity : RelevantEntityPattern)
    (groupPath : List String) : Option RelevantEntityPattern :=
  if entity.indices.length != entity.path.length ||
      !groupPath.isPrefixOf entity.path then
    none
  else
    some { path := groupPath, indices := entity.indices.take groupPath.length }

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

/-- Project one caller identifier onto the operand field for wildcard-only consumers such as value counts and missing-key lookup. Partial list quantifiers instead combine identifiers through `ValidationRelevanceScope.coversDeclaredFieldExtent` (spec/10 §5). -/
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

/-- Retain the caller identifiers one projection keeps inside the current iteration subtree, then
    remove wildcard-dominated siblings. The projection is the only thing a reduced-universal gate's
    users choose. -/
def retainedExtentPatterns (entities : List RelevantEntityPattern)
    (model : FlatModel) (boundLevels : List RepeatableLevel) (outer : Env)
    (project : RelevantEntityPattern → Option RelevantEntityPattern) :
    List RelevantEntityPattern :=
  ((entities.filterMap project).filter
    fun entity => entity.matchesBoundSubtree model boundLevels outer)
    |> RelevantEntityPattern.reduceWildcardDominance

/-- The reduced-universal test: the retained set is nonempty and every identifier in it wildcards
    every level reopened from the first star. -/
def reducedUniversalCovers (retained : List RelevantEntityPattern) (model : FlatModel)
    (reopenedLevels : List RepeatableLevel) : Bool :=
  !retained.isEmpty && retained.all fun entity => entity.wildcardsLevels model reopenedLevels

/-- Prepare one all-rows operand's target-specific identifier set: expand ancestors, retain the current iteration subtree, then remove wildcard-dominated siblings. -/
def aggregateExtentPatterns (entities : List RelevantEntityPattern)
    (model : FlatModel) (targetPath : List String)
    (boundLevels : List RepeatableLevel) (outer : Env) :
    List RelevantEntityPattern :=
  retainedExtentPatterns entities model boundLevels outer (·.projectOntoTarget? targetPath)

/-- All-rows aggregate relevance is universal over the normalized retained identifiers. -/
def coversAggregateExtent (scope : ValidationRelevanceScope) (model : FlatModel)
    (targetPath : List String) (boundLevels reopenedLevels : List RepeatableLevel)
    (outer : Env) : Bool :=
  match scope with
  | .full => true
  | .partialSet entities =>
      reducedUniversalCovers (aggregateExtentPatterns entities model targetPath boundLevels outer)
        model reopenedLevels

/-- The counted group's own identifiers for `NumberOfFilledGroups`: the relevant identifiers at or
    above the group together with every relevant descendant cut back to the group's depth
    ([inbound](../../docs/sources/inbound-handbacks.md#inbound-2026-09-24b-kf464-partial-group-count)). -/
def groupCountPatterns (entities : List RelevantEntityPattern)
    (model : FlatModel) (groupPath : List String)
    (boundLevels : List RepeatableLevel) (outer : Env) :
    List RelevantEntityPattern :=
  retainedExtentPatterns entities model boundLevels outer fun entity =>
    (entity.projectOntoTarget? groupPath).orElse fun _ => entity.cutBackTo? groupPath

/-- The group count's extent gate is the reduced-universal test over the counted group's own
    identifiers, so a concrete coordinate left at a starred level makes the count undecidable even
    when every instance is wholly covered. -/
def coversGroupCountExtent (scope : ValidationRelevanceScope) (model : FlatModel)
    (groupPath : List String) (boundLevels reopenedLevels : List RepeatableLevel)
    (outer : Env) : Bool :=
  match scope with
  | .full => true
  | .partialSet entities =>
      reducedUniversalCovers (groupCountPatterns entities model groupPath boundLevels outer)
        model reopenedLevels

/-- Wildcard-only extent policy for value counts, missing-key lookup and legacy adapters: concrete siblings do not cancel a qualifying wildcard. Partial list quantifiers use `coversDeclaredFieldExtent` to combine concrete coverage (spec/10 §5). -/
def coversValueListExtent (scope : ValidationRelevanceScope) (model : FlatModel)
    (targetPath : List String) (boundLevels reopenedLevels : List RepeatableLevel)
    (outer : Env) : Bool :=
  match scope with
  | .full => true
  | .partialSet entities => entities.any fun entity =>
      entity.coversValueListExtent model targetPath boundLevels reopenedLevels outer

private inductive DeclaredCoverageAxis where
  | ignored
  | fixed (coordinate : Nat)
  | wildcard
  | finite (capacity : Nat)

private def coverageTails (selector : RelevanceIndex)
    (patterns : List (List RelevanceIndex)) : List (List RelevanceIndex) :=
  patterns.filterMap fun
    | .all :: remaining => some remaining
    | .concrete coordinate :: remaining =>
        if selector == .concrete coordinate then some remaining else none
    | [] => none

/-- Concrete coordinates named by the input patterns are the only distinct cases. Every other
coordinate sees exactly the wildcard tails, so capacities never require a Cartesian materialization. -/
private def declaredCoverage : List DeclaredCoverageAxis → List (List RelevanceIndex) → Bool
  | [], patterns => patterns.any List.isEmpty
  | .ignored :: remaining, patterns =>
      declaredCoverage remaining (patterns.filterMap fun
        | _ :: tail => some tail
        | [] => none)
  | .fixed coordinate :: remaining, patterns =>
      declaredCoverage remaining (coverageTails (.concrete coordinate) patterns)
  | .wildcard :: remaining, patterns => declaredCoverage remaining (coverageTails .all patterns)
  | .finite capacity :: remaining, patterns =>
      let named := (patterns.filterMap fun pattern => match pattern.head? with
        | some (.concrete coordinate) => if 0 < coordinate && coordinate ≤ capacity then some coordinate else none
        | _ => none).eraseDups
      named.all (fun coordinate => declaredCoverage remaining (coverageTails (.concrete coordinate) patterns)) &&
        (named.length == capacity || declaredCoverage remaining (coverageTails .all patterns))

/-- Group-absence coverage consumes the terminal field's identity, but not its coordinate;
declared-field coverage retains that coordinate (KF120 fixed-suffix calibration, 2026-10-12). -/
private def coversDeclaredFieldExtentUsing (terminal : DeclaredCoverageAxis) (scope : ValidationRelevanceScope) (model : FlatModel)
    (targetPath : List String) (reopenedLevels : List RepeatableLevel) (outer : Env)
    (missingParent : Option RepeatableLevel := none) : Except StarAddressingError Bool := do
  let .partialSet entities := scope | return true
  let mut axes : List DeclaredCoverageAxis := []
  let mut path : GroupPath := []
  for segment in targetPath do
    path := path ++ [segment]
    let axis ← match model.repeatableGroups.find? (·.path == path) with
      | none => pure (if path == targetPath then terminal else .fixed 1)
      | some group =>
          if missingParent == some group.level then pure .wildcard
          else if reopenedLevels.contains group.level then
            pure (match group.repeatability with | none => .wildcard | some capacity => .finite capacity)
          else do
            let coordinate ← (outer.bindingAt group.level).mapError EnvBindingError.toStarAddressingError
            pure (.fixed coordinate)
    axes := axes ++ [axis]
  pure (declaredCoverage axes (entities.filterMap fun entity =>
    (entity.projectOntoTarget? targetPath).map (·.indices)))

/-- Coverage of every declared slot by the union of relevant identifiers (spec/10 §5).
Finite capacity permits concrete coverage; unbounded capacity and a missing selected parent
still require wildcard coverage. The partition uses authored patterns rather than declared size. -/
def coversDeclaredFieldExtent (scope : ValidationRelevanceScope) (model : FlatModel)
    (targetPath : List String) (reopenedLevels : List RepeatableLevel) (outer : Env)
    (missingParent : Option RepeatableLevel := none) : Except StarAddressingError Bool :=
  coversDeclaredFieldExtentUsing (.fixed 1) scope model targetPath reopenedLevels outer missingParent

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

/-- Derive the kernel's three-level relevance for one concrete group instance. Any intersecting selection supplies partial visibility; definite absence additionally requires an ancestor group selection or complete union coverage of every declared descendant. Finite deeper levels accept all concrete positions; unbounded levels require a wildcard (spec/10 §5). -/
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
          let reopened := (model.repeatableGroups.filter fun group =>
            groupPath.length < group.path.length && groupPath.isPrefixOf group.path).map (·.level)
          (coversDeclaredFieldExtentUsing .ignored scope model declaration.path reopened environment).toOption.getD false then
        .fullyRelevant
      else
        .partlyRelevant

end ValidationRelevanceScope

end A12Kernel
