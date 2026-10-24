import A12Kernel.Elaboration.ValidationRelevance
import A12Kernel.Semantics.GroupPresence
import A12Kernel.Semantics.StarAddressing

/-! # Checked general star-path lowering

This boundary resolves structured group-segment stars against one validated `FlatModel`, derives the exact outer-to-inner repeatable axes from the field declaration, and identifies the first reopened axis. Runtime rows remain owned by `StarAddressing`.
-/

namespace A12Kernel

/-- Filter iteration shares maxima across group names at the same model depth, including blank
rows. Fixed intervening groups count toward depth; their absence from `Env` must not merge depths.
The caller supplies phase-visible rows (Kernel GroupFillCache; KF528). -/
def FlatModel.filterDepthMaximum (model : FlatModel) (rows : List RowAddr)
    (level : RepeatableLevel) : Nat :=
  match model.repeatableGroupAtLevel? level with
  | none => 1
  | some group => rows.foldl (fun maximum row =>
      match model.repeatableGroupAtLevel? row.group with
      | some other => if other.path.length == group.path.length then
          max maximum (row.path.getLast?.getD 1) else maximum
      | none => maximum) 1

def FlatModel.filterEnvironments (model : FlatModel) (path : StarPath)
    (rows : List RowAddr) (outer : Env) (sparse : Bool := false) :
    Except StarAddressingError (List Env) :=
  path.boundedFilterEnvironments outer (model.filterDepthMaximum rows) sparse

/-- Construct the consumer's traversal before evaluating its filter. Sparse consumers retain
occupancy for the predicate-dependent cursor; unresolved policies refuse large domains. -/
def FlatModel.filterTraversal (model : FlatModel) (path : StarPath)
    (rows : List RowAddr) (outer : Env) (mode : FilterTraversalMode := .sparse) :
    Except StarAddressingError FilterTraversal := do
  if mode == .requireSmall then
    return { candidates := ← model.filterEnvironments path rows outer true }
  let candidates ← model.filterEnvironments path rows outer
  if mode == .dense || candidates.length ≤ 100 then return { candidates }
  let some axis := path.axes.getLast? | throw (.unsupportedGroupOperand [])
  let some group := model.repeatableGroupAtLevel? axis.level
    | throw (.unsupportedGroupOperand [])
  let levels := (List.range group.path.length).map fun depth =>
    (model.repeatableGroups.find? (·.path == group.path.take (depth + 1))).map (·.level)
  let occupied := rows.filterMap fun row => do
    let rowGroup ← model.repeatableGroupAtLevel? row.group
    pure (model.groupCoordinates rowGroup.path
      ((model.repeatableScopeForGroupPath rowGroup.path).zip row.path))
  pure { candidates, occupancy := some { levels, occupied } }

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

/-- A parser-independent group path retaining every authored wildcard marker. -/
structure SurfaceStarGroupPath where
  base : PathBase
  groups : List SurfaceStarGroupSegment
  deriving Repr, DecidableEq

/-- `groups` with only its last segment starred, the shape a plain `Rows*` operand authors. -/
def SurfaceStarGroupPath.terminallyStarred (base : PathBase) (groups : GroupPath) :
    SurfaceStarGroupPath :=
  { base
    groups := groups.dropLast.map ({ name := · }) ++
      groups.getLast?.toList.map ({ name := ·, starred := true }) }

namespace SurfaceStarFieldPath

def toFieldPath (source : SurfaceStarFieldPath) : SurfaceFieldPath :=
  { base := source.base
    turningPoint := source.turningPoint
    groups := source.groups.map (·.name)
    field := source.field }

end SurfaceStarFieldPath



inductive StarPathElabError where
  | resolve (error : ResolveError)
  | wildcardOnNonrepeatable (path : GroupPath)
  | missingWildcard (path : List String)
  | iterationBelowWildcard (path : GroupPath)
  /-- A level left unstarred below the first star, placed outside the declaring group by the written
  field, so the containment gate answers it; `StarPathElabError.placeBelowStar` produces it. -/
  | containmentBelowStar (unbound : UnboundOperandLevel)
  | addressing (error : StarAddressingError)
  | incoherentCore
  deriving Repr, DecidableEq

/-- The classes a starred path owns whichever carrier reads it: the resolver's name-failure classes,
and a star landing on anything but a repeatable group, which pre-empts every slot's own wildcard gate
([checkpoint](../../docs/sources/path-resolution-class-probes.md#src-starred-path-segment-order)).

A repeatable level left unstarred **below** the first star is `noWildcard` on every carrier measured
and both arms, whatever binds the level and whether or not its group is index-keyed, wherever the
written field lies inside the declaring group; outside it the containment gate answers first, which
`StarPathElabError.placeBelowStar` asks for a computation's fixed target and a validation's error
field. The Kernel judges each level while it reads the reference
([`kf440`](../../../a12-rulekit/docs/KERNEL-FINDINGS.md#kf440)), so this class also answers ahead of
a carrier's own star bar, as `AllGroupsFilled` shows
([checkpoint](../../docs/sources/group-list-and-capacity-probes.md#src-computation-star-binding-gate)).
A missing *first* star stays with the carrier, because the class it draws is the slot's. -/
def StarPathElabError.diagnostic? : StarPathElabError → Option KernelStaticDiagnostic
  | .resolve error => error.diagnostic?
  | .wildcardOnNonrepeatable _ => some .invalidWildcard
  | .iterationBelowWildcard _ => some .noWildcard
  | .containmentBelowStar unbound => unbound.diagnostic?
  | _ => none

/-- Place a star's refusal by the written field — a computation's fixed target or a validation's
error field. With the written field outside the declaring group, a level the star leaves unstarred
below its first star meets the containment gate ahead of the missing-star class, measured on the
validation carriers two checkpoints list and on the computation arm
([inbound](../../docs/sources/inbound-handbacks.md#inbound-2026-09-24d-star-containment),
[checkpoint](../../docs/sources/group-list-and-capacity-probes.md#src-validation-below-star-placement),
[kinds checkpoint](../../docs/sources/group-list-and-capacity-probes.md#src-validation-below-star-placement-kinds)).
A written field inside the declaring group, which a validation carrier entry assumes when its caller
names none, leaves every refusal as it was. -/
def StarPathElabError.placeBelowStar (model : FlatModel) (declaringGroup writtenGroup : GroupPath) :
    StarPathElabError → StarPathElabError
  | error@(.iterationBelowWildcard path) =>
      match model.repeatableGroups.find? (·.path == path) with
      | some group =>
          let unbound := model.unboundOperandLevel declaringGroup writtenGroup group.level
          match unbound.placement with
          | .outside => .containmentBelowStar unbound
          | .contained => error
      | none => error
  | error => error

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
  let resolved ← checked.path.resolveInCapacity document outer
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
  let resolved ← checked.path.resolveInCapacity document outer
  pure (checked.selectedPartialValueListSide resolved outer scope classify)

end CheckedStarFieldPath

private structure MarkedStarAxis where
  path : GroupPath
  axis : StarAxis
  starred : Bool

/-- The first starred segment naming a declared group or field that is not a repeatable group,
    scanned only while every segment names something, because a segment's name is read before its star
    and a segment naming nothing stops the walk. Every planner caller has resolved the path already, so
    there it reaches every segment; a starred field or group path's lookup miss asks it of the prefix
    that resolves. -/
def firstStarOnNamedNonrepeatable? (model : FlatModel) :
    GroupPath → List SurfaceStarGroupSegment → Option (List String)
  | _, [] => none
  | pathPrefix, segment :: rest =>
      let path := pathPrefix ++ [segment.name]
      -- A star on a declared group without a field draws the wildcard class ahead of its emptiness
      -- (k22-static-classes-2026-10-24, `s7-star1`, `s11-c8`).
      if !(model.hasGroupPath path || model.declaresEmptyGroup path ||
          model.fields.any (·.path == path)) then none
      else if segment.starred && !model.repeatableGroups.any (·.path == path) then some path
      else firstStarOnNamedNonrepeatable? model path rest

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
  match firstStarOnNamedNonrepeatable? model basePath groups with
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
  cases hWildcard : firstStarOnNamedNonrepeatable? model basePath groups with
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
  cases hWildcard : firstStarOnNamedNonrepeatable? model basePath groups with
  | some path => simp
  | none =>
      simpa using
        planFromMarkedAxes_never_incoherentCore
          (markedAxes model []
            (basePath.map (fun name => ({ name } : SurfaceStarGroupSegment)) ++ groups))
          targetPath

/-- Resolve the field a starred path names, answering in the Kernel's segment order. Only a lookup
    miss can follow a readable star: the declaring group, the path's shape and the parent steps are
    judged before any group segment, an unknown root is the first segment missing, and model
    validation refuses the duplicate declaration behind an ambiguous one. So a miss is re-read for an
    earlier star landing on a nonrepeatable segment, which answers first
    ([checkpoint](../../docs/sources/path-resolution-class-probes.md#src-starred-path-segment-order)).
    A starred first segment the short-name fallback binds to a field is such a star too
    ([inbound](../../docs/sources/inbound-handbacks.md#inbound-2026-09-24c-path-walk)). -/
private def starredMissError (model : FlatModel) (declaringGroup : GroupPath)
    (source : SurfaceStarFieldPath) (reference : SurfaceFieldPath) : StarPathElabError :=
  let base? := match source.base with
    | .absolute => some []
    | .relative parents =>
        (GroupPath.walkUp declaringGroup parents).toOption.filter
          (GroupPath.matchesTurningPoint · source.turningPoint)
  match base?.bind (firstStarOnNamedNonrepeatable? model · source.groups) with
  | some path => .wildcardOnNonrepeatable path
  | none =>
      match source.groups.head?, model.shortNameFirstSegmentField? declaringGroup reference with
      | some { starred := true, .. }, some declaration => .wildcardOnNonrepeatable declaration.path
      | _, _ => .resolve (.invalidEntity reference)

/-- Resolve starred spelling without imposing the complete star plan; filter-local reads defer
iteration checks until the enclosing body walk (spec/07 §3). -/
def resolveStarFieldDeclaration (model : FlatModel) (declaringGroup : GroupPath)
    (source : SurfaceStarFieldPath) : Except StarPathElabError FlatFieldDecl :=
  match model.resolveFieldDeclarationUnchecked declaringGroup source.toFieldPath with
  | .ok declaration => .ok declaration
  | .error (.invalidEntity reference) =>
      .error (starredMissError model declaringGroup source reference)
  | .error error => .error (.resolve error)

private theorem resolveStarFieldDeclaration_resolved
    {model : FlatModel} {declaringGroup : GroupPath} {source : SurfaceStarFieldPath}
    {declaration : FlatFieldDecl}
    (resolved : resolveStarFieldDeclaration model declaringGroup source = .ok declaration) :
    model.resolveFieldDeclarationUnchecked declaringGroup source.toFieldPath = .ok declaration := by
  unfold resolveStarFieldDeclaration at resolved
  split at resolved <;> first | (cases resolved; assumption) | cases resolved

/-- Resolve a legal starred field path into the exact model-owned ancestry consumed by `StarAddressing`. A relative turning point may precede later stars; the first star and every deeper repeatable level must be explicitly starred. -/
def elaborateStarFieldPath (model : FlatModel) (declaringGroup : GroupPath)
    (source : SurfaceStarFieldPath) :
    Except StarPathElabError (CheckedStarFieldPath model) :=
  match hModel : model.validate with
  | .error error => .error (.resolve error)
  | .ok () => do
      let declaration ← resolveStarFieldDeclaration model declaringGroup source
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
  · cases hResolved : resolveStarFieldDeclaration model declaringGroup source with
    | error _ =>
        simp only [hResolved, bind, Except.bind] at elaborated
        cases elaborated
    | ok declaration =>
        exact FlatModel.resolveFieldDeclarationUnchecked_declaringGroupValid
          (resolveStarFieldDeclaration_resolved hResolved)

end A12Kernel
