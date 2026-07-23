import A12Kernel.Elaboration.Flat
import A12Kernel.Semantics.Iteration

/-! # Shared checked group-reference and one-group Number boundaries -/

namespace A12Kernel

/-- A structured group path after concrete syntax has decoded separators and quoting. -/
structure SurfaceGroupPath where
  base : PathBase
  /-- Optional explicit name of the group reached by a positive parent count. -/
  turningPoint : Option String := none
  groups : List String
  deriving Repr, DecidableEq

/-- A group-valued entity after concrete syntax has distinguished an ordinary path from the reserved `RuleGroup` keyword. The keyword is not a path base and cannot carry descent segments. Its wildcard bit is retained solely so checked lowering can report the kernel-specific error. -/
inductive SurfaceGroupReference where
  | path (reference : SurfaceGroupPath)
  | ruleGroup (starred : Bool)
  deriving Repr, DecidableEq

inductive GroupReferenceOrigin where
  | path
  | ruleGroup
  deriving Repr, DecidableEq

/-- A resolved group keeps authored origin for stable Transform/Explain consumers instead of erasing `RuleGroup` into an ordinary path. -/
structure ResolvedGroupReference where
  path : GroupPath
  origin : GroupReferenceOrigin
  deriving Repr, DecidableEq

/-- A direct-child field path with exactly one explicitly identified starred group segment. -/
structure SurfaceSingleStarFieldPath where
  base : PathBase
  /-- Optional explicit name of the parent-walk turning point. Parent navigation remains illegal for this one-star shape. -/
  turningPoint : Option String := none
  groupsBeforeStar : List String
  starredGroup : String
  field : String
  deriving Repr, DecidableEq

/-- Fail-closed errors shared by one-group path and direct-child Number resolution. -/
inductive SingleGroupElabError where
  | resolve (error : ResolveError)
  | invalidGroupReference (reference : SurfaceGroupPath)
  | wildcardOnRuleGroup
  | wildcardWithParentNavigation (parents : Nat)
  | fieldNotNumber (path : List String)
  | fieldOutsideGroup (fieldPath expectedGroup : List String)
  | fieldScopeMismatch (fieldPath : List String)
      (expected actual : List RepeatableLevel)
  deriving Repr, DecidableEq

/-- Resolve one structured group reference against its declaring group. -/
def SurfaceGroupPath.resolveAgainst (reference : SurfaceGroupPath)
    (declaringGroup : GroupPath) : Except SingleGroupElabError GroupPath := do
  if !GroupPath.isValid declaringGroup then
    throw (.resolve (.invalidRuleGroup declaringGroup))
  if !reference.groups.all (!·.isEmpty) ||
      !reference.turningPoint.all (!·.isEmpty) ||
      !reference.base.allowsTurningPoint reference.turningPoint then
    throw (.invalidGroupReference reference)
  let path ← match reference.base with
    | .absolute => pure reference.groups
    | .relative parents =>
        let base ← GroupPath.walkUp declaringGroup parents |>.mapError .resolve
        if !base.matchesTurningPoint reference.turningPoint then
          throw (.invalidGroupReference reference)
        else
          pure (base ++ reference.groups)
  if GroupPath.isValid path then pure path else throw (.invalidGroupReference reference)

/-- Resolve either an ordinary group path or the non-prefix `RuleGroup` keyword. -/
def SurfaceGroupReference.resolveAgainst (reference : SurfaceGroupReference)
    (declaringGroup : GroupPath) : Except SingleGroupElabError ResolvedGroupReference := do
  match reference with
  | SurfaceGroupReference.path groupPath =>
      let resolvedPath ← groupPath.resolveAgainst declaringGroup
      pure { path := resolvedPath, origin := .path }
  | SurfaceGroupReference.ruleGroup starred =>
      if !GroupPath.isValid declaringGroup then
        throw (.resolve (.invalidRuleGroup declaringGroup))
      if starred then throw .wildcardOnRuleGroup
      pure { path := declaringGroup, origin := .ruleGroup }

namespace ResolvedGroupReference

/-- Group-valued conditions reference every field in the resolved group subtree. In particular, `RuleGroup` therefore satisfies the error-field reference gate for a field in its own rule group. -/
def referencesField (reference : ResolvedGroupReference)
    (model : FlatModel) (field : FieldId) : Bool :=
  match model.lookupUniqueId field with
  | .ok declaration => reference.path.isPrefixOf declaration.groupPath
  | .error _ => false

/-- Whether a resolved group denotes a model root. Operator-specific admission decides whether that root is legal. -/
def isRoot (reference : ResolvedGroupReference) : Bool :=
  reference.path.length == 1

/-- Ordinary paths are fixed only outside every repeatable scope; `RuleGroup` binds the already-selected rule instance even when that instance belongs to a repeatable group. -/
def fixedWellFormedBool (reference : ResolvedGroupReference)
    (model : FlatModel) (declaringGroup : GroupPath) : Bool :=
  model.hasGroupPath reference.path &&
    match reference.origin with
    | .path => (model.repeatableScopeForGroupPath reference.path).isEmpty
    | .ruleGroup => reference.path == declaringGroup

/-- Two group-valued operands overlap when either denotes the other or one of its descendants. -/
def overlaps (left right : ResolvedGroupReference) : Bool :=
  left.path.isPrefixOf right.path || right.path.isPrefixOf left.path

end ResolvedGroupReference

/-- Shared failures while resolving one group reference that must denote either a nonrepeatable ordinary group or the already-selected `RuleGroup` instance. -/
inductive FixedGroupReferenceError where
  | reference (error : SingleGroupElabError)
  | unknownGroup (path : GroupPath)
  | repeatableGroupRequiresAddress (path : GroupPath)
  deriving Repr, DecidableEq

/-- Resolve one fixed group operand without applying an operator-specific root, arity, duplicate, or overlap rule. -/
def FlatModel.resolveFixedGroupReference (model : FlatModel)
    (declaringGroup : GroupPath) (surface : SurfaceGroupReference) :
    Except FixedGroupReferenceError ResolvedGroupReference := do
  let resolved ← surface.resolveAgainst declaringGroup |>.mapError .reference
  if !model.hasGroupPath resolved.path then
    throw (.unknownGroup resolved.path)
  match resolved.origin with
  | .path =>
      if (model.repeatableScopeForGroupPath resolved.path).isEmpty then
        pure resolved
      else
        throw (.repeatableGroupRequiresAddress resolved.path)
  | .ruleGroup => pure resolved

namespace ResolvedGroupReferences

/-- Find the first declaration-ordered duplicate or ancestor/descendant overlap. -/
def firstOverlap? : List ResolvedGroupReference →
    Option (GroupPath × GroupPath)
  | [] => none
  | first :: rest =>
      match rest.find? (first.overlaps ·) with
      | some overlapping => some (first.path, overlapping.path)
      | none => firstOverlap? rest

/-- All fixed group references remain coherent with the same validated model and declaring rule instance. -/
def wellFormedBool (references : List ResolvedGroupReference)
    (model : FlatModel) (declaringGroup : GroupPath) : Bool :=
  references.all (·.fixedWellFormedBool model declaringGroup)

end ResolvedGroupReferences

/-- Validate one single-star field shape and recover its authored group reference. -/
def SurfaceSingleStarFieldPath.groupReference
    (reference : SurfaceSingleStarFieldPath) : Except SingleGroupElabError SurfaceGroupPath := do
  if !reference.groupsBeforeStar.all (!·.isEmpty) || reference.starredGroup.isEmpty ||
      reference.field.isEmpty then
    let groupReference : SurfaceGroupPath :=
      { base := reference.base,
        turningPoint := reference.turningPoint
        groups := reference.groupsBeforeStar ++ [reference.starredGroup] }
    throw (.invalidGroupReference groupReference)
  match reference.base with
  | .relative parents =>
      if parents > 0 then throw (.wildcardWithParentNavigation parents)
  | .absolute => pure ()
  pure {
    base := reference.base
    turningPoint := reference.turningPoint
    groups := reference.groupsBeforeStar ++ [reference.starredGroup]
  }

/-- Resolve a Number field that must be a direct child of one exact repeatable group. -/
def FlatModel.resolveNumberInGroup (model : FlatModel)
    (declaringGroup : GroupPath) (group : RepeatableGroupDecl)
    (reference : SurfaceFieldPath) :
    Except SingleGroupElabError (FlatFieldDecl × FlatNumberField) := do
  let declaration ←
    (model.resolveFieldDeclarationUnchecked declaringGroup reference).mapError .resolve
  if declaration.groupPath != group.path then
    throw (.fieldOutsideGroup declaration.path group.path)
  let expectedScope := [group.level]
  if declaration.repeatableScope != expectedScope then
    throw (.fieldScopeMismatch declaration.path expectedScope declaration.repeatableScope)
  let field ← match declaration.toNumberField? with
    | some field => pure field
    | none => throw (.fieldNotNumber declaration.path)
  pure (declaration, field)

/-- A Number field is admitted only when its unique declaration is a direct child of the exact repeatable group, carries exactly that singleton scope, and has identical numeric metadata. -/
def FlatModel.admitsSingleGroupNumber (model : FlatModel)
    (group : RepeatableGroupDecl) (field : FlatNumberField) : Bool :=
  match model.lookupUniqueId field.id with
  | .error _ => false
  | .ok declaration =>
      declaration.groupPath == group.path &&
      declaration.repeatableScope == [group.level] &&
      (FlatField.number field).matchesDecl declaration

structure RawSingleGroupContext where
  candidates : List RowIndex
  read : RowIndex → FieldId → RawCell

inductive SingleGroupContextError where
  | zeroCandidate (row : RowIndex)
  | duplicateCandidate (row : RowIndex)
  deriving Repr, DecidableEq

/-- Candidate row identities are 1-based and unique. Reject malformed topology before any cells are read or any rule is evaluated. -/
def RawSingleGroupContext.validate (raw : RawSingleGroupContext) :
    Except SingleGroupContextError Unit := do
  match raw.candidates.find? (· == 0) with
  | some row => throw (.zeroCandidate row)
  | none => pure ()
  match RowIndex.firstDuplicate? raw.candidates with
  | some row => throw (.duplicateCandidate row)
  | none => pure ()

/-- Compile a raw one-group document view with the exact declarations used by elaboration. Cross-group, wrong-scope, missing, and ambiguous IDs fail closed as malformed. -/
def FlatModel.checkSingleGroupContext (model : FlatModel)
    (group : RepeatableGroupDecl) (raw : RawSingleGroupContext) :
    SingleGroupValidationContext where
  group := group.level
  candidates := raw.candidates
  read row id :=
    match model.lookupUniqueId id with
    | .ok declaration =>
        if declaration.groupPath == group.path &&
            declaration.repeatableScope == [group.level] then
          declaration.checkRaw (raw.read row id)
        else
          malformedCheckedCell
    | .error _ => malformedCheckedCell

end A12Kernel
