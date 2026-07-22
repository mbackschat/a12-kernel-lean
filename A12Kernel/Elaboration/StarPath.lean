import A12Kernel.Elaboration.Flat
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
  { base := source.base, groups := source.groups.map (·.name), field := source.field }

end SurfaceStarFieldPath

namespace RelevantEntityPattern

private def actualIndex? (model : FlatModel) (environment : Env)
    (path : GroupPath) : Option Nat :=
  match model.repeatableGroups.find? fun group => group.path == path with
  | none => some 1
  | some group =>
      match environment.find? fun binding => binding.1 == group.level with
      | none => none
      | some binding => some binding.2

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

private def repeatablePrefixesCovered (model : FlatModel) :
    GroupPath → List String → List RelevanceIndex → Bool
  | _, [], [] => true
  | pathPrefix, segment :: segments, index :: indices =>
      let path := pathPrefix ++ [segment]
      let currentCovered :=
        !model.repeatableGroups.any (fun group => group.path == path) ||
          index == .all
      currentCovered && repeatablePrefixesCovered model path segments indices
  | _, _, _ => false

/-- Whether this one entity makes every row of the target field's starred ancestry relevant. The entity must be the target or an ancestor and must wildcard every repeatable level it names; group descent covers deeper levels. -/
def coversAllRows (entity : RelevantEntityPattern) (model : FlatModel)
    (targetPath : List String) : Bool :=
  entity.path.isPrefixOf targetPath &&
    repeatablePrefixesCovered model [] entity.path entity.indices

/-- Whether this one entity covers a concrete target instance. Exact fields and ancestor groups share the same prefix/index rule; wildcard indices match any concrete coordinate. -/
def coversCell (entity : RelevantEntityPattern) (model : FlatModel)
    (targetPath : List String) (environment : Env) : Bool :=
  entity.path.isPrefixOf targetPath &&
    cellPrefixMatches model environment [] entity.path entity.indices

end RelevantEntityPattern

namespace ValidationRelevanceScope

/-- All-rows aggregate relevance is an operator-level path fact. Enumerating every concrete row does not substitute for one wildcard-covering entity. -/
def coversAllRows (scope : ValidationRelevanceScope) (model : FlatModel)
    (targetPath : List String) : Bool :=
  match scope with
  | .full => true
  | .partialSet entities => entities.any fun entity => entity.coversAllRows model targetPath

/-- Per-cell relevance retains concrete row identity and ancestor descent. Unlike all-rows relevance, different concrete entities may cover different reached cells. -/
def coversCell (scope : ValidationRelevanceScope) (model : FlatModel)
    (targetPath : List String) (environment : Env) : Bool :=
  match scope with
  | .full => true
  | .partialSet entities =>
      entities.any fun entity => entity.coversCell model targetPath environment

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

/-- Whether this checked starred field is completely relevant for an all-rows validation consumer. This gate does not apply to order-aware `FirstFilledValue`. -/
def CheckedStarFieldPath.allRowsRelevant (checked : CheckedStarFieldPath model)
    (scope : ValidationRelevanceScope) : Bool :=
  scope.coversAllRows model checked.declaration.path

/-- Whether one topology-produced concrete field instance is relevant to this validation call. -/
def CheckedStarFieldPath.cellRelevant (checked : CheckedStarFieldPath model)
    (scope : ValidationRelevanceScope) (environment : Env) : Bool :=
  scope.coversCell model checked.declaration.path environment

namespace CheckedStarFieldPath

private def bindingOverLimit (axis : StarAxis)
    (binding : RepeatableLevel × Nat) : Bool :=
  axis.level == binding.1 && match axis.repeatability with
    | none => false
    | some limit => binding.2 > limit

/-- Whether one topology-produced leaf environment lies under any over-capacity repeatable ancestor. This structural check is independent of the terminal field kind. -/
def environmentOverLimit (checked : CheckedStarFieldPath model)
    (environment : Env) : Bool :=
  (checked.path.axes.zip environment).any fun binding =>
    bindingOverLimit binding.1 binding.2

/-- Apply the declaration-owned scalar checker unless structural over-repetition is the sole formal cause. Every typed star consumer shares this checked-cell boundary. -/
def checkedCell (checked : CheckedStarFieldPath model)
    (read : Env → FieldId → RawCell) (environment : Env) : CheckedCell :=
  let scalar := checked.declaration.checkRaw
    (read environment checked.declaration.id)
  if checked.environmentOverLimit environment then
    { scalar with parsed := none, findings := [.overRepetition] }
  else
    scalar

/-- Resolve canonical topology once and classify every leaf in its established order. -/
def resolvedValueListSide (checked : CheckedStarFieldPath model)
    (document : Document) (outer : Env) (classify : Env → ValueListCell kind) :
    Except StarAddressingError (ResolvedValueListSide kind) := do
  let resolved ← checked.path.resolve document outer
  pure (resolved.toResolvedSide classify)

/-- Retain only relevant concrete cells before invoking the kind-specific classifier, while recording whether the star's complete extent is wildcard-covered. Concrete enumeration of every current row does not establish that future/absent rows are relevant. -/
def selectedPartialValueListSide (checked : CheckedStarFieldPath model)
    (resolved : ResolvedStarTopology) (scope : ValidationRelevanceScope)
    (classify : Env → ValueListCell kind) :
    ResolvedValueListQuantifierSide kind :=
  let relevant := resolved.environments.filter fun environment =>
    checked.cellRelevant scope environment
  { side := {
      cells := relevant.map classify
      hasUninstantiatedTail := resolved.domain.hasOpenTail
      hasHaving := false }
    hasNonRelevant := !checked.allRowsRelevant scope }

/-- Resolve canonical topology once, then apply per-cell relevance before kind-specific classification. -/
def resolvedPartialValueListSide (checked : CheckedStarFieldPath model)
    (document : Document) (outer : Env) (scope : ValidationRelevanceScope)
    (classify : Env → ValueListCell kind) :
    Except StarAddressingError (ResolvedValueListQuantifierSide kind) := do
  let resolved ← checked.path.resolve document outer
  pure (checked.selectedPartialValueListSide resolved scope classify)

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

/-- Derive the one shared checked star plan after the caller has resolved the terminal field or group. A relative base is supplied separately so its named repeatable ancestors remain fixed before the first authored star. -/
def elaborateStarPathPlan (model : FlatModel) (basePath : GroupPath)
    (groups : List SurfaceStarGroupSegment) (targetPath : List String) :
    Except StarPathElabError CheckedStarPlan := do
  match firstInvalidWildcard? model basePath groups with
  | some path => throw (.wildcardOnNonrepeatable path)
  | none => pure ()
  let baseSegments := basePath.map fun name => ({ name } : SurfaceStarGroupSegment)
  let marked := markedAxes model [] (baseSegments ++ groups)
  let firstStar ← match firstStarredAxis? marked 0 with
    | none => throw (.missingWildcard targetPath)
    | some index => pure index
  match firstUnstarredAxis? (marked.drop firstStar) with
  | some path => throw (.iterationBelowWildcard path)
  | none => pure ()
  let path : StarPath := { axes := marked.map (·.axis), firstStar }
  if hFirstStar : path.firstStar < path.axes.length then
    match hPath : path.validate with
    | .error error => throw (.addressing error)
    | .ok () => pure {
        path
        firstStarWithin := hFirstStar
        pathValid := by rw [hPath]; rfl }
  else
    throw .incoherentCore

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

end A12Kernel
