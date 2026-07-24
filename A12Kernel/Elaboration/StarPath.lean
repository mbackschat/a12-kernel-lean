import A12Kernel.Elaboration.Flat.Context
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

/-- Repeatable levels strictly above the first star remain fixed by the surrounding rule environment. The starred level and every deeper axis stay operand-local. -/
def bindingScope (checked : CheckedStarFieldPath model) :
    List RepeatableLevel :=
  (checked.path.axes.take checked.path.firstStar).map (·.level)

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

end A12Kernel
