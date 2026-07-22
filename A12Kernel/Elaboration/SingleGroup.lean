import A12Kernel.Elaboration.Flat
import A12Kernel.Semantics.Iteration

/-! # Shared checked one-group Number boundaries -/

namespace A12Kernel

/-- A structured group path after concrete syntax has decoded separators and quoting. -/
structure SurfaceGroupPath where
  base : PathBase
  groups : List String
  deriving Repr, DecidableEq

/-- A direct-child field path with exactly one explicitly identified starred group segment. -/
structure SurfaceSingleStarFieldPath where
  base : PathBase
  groupsBeforeStar : List String
  starredGroup : String
  field : String
  deriving Repr, DecidableEq

/-- Fail-closed errors shared by one-group path and direct-child Number resolution. -/
inductive SingleGroupElabError where
  | resolve (error : ResolveError)
  | invalidGroupReference (reference : SurfaceGroupPath)
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
  if !reference.groups.all (!·.isEmpty) then
    throw (.invalidGroupReference reference)
  let path ← match reference.base with
    | .absolute => pure reference.groups
    | .relative parents =>
        pure ((← GroupPath.walkUp declaringGroup parents |>.mapError .resolve) ++ reference.groups)
  if GroupPath.isValid path then pure path else throw (.invalidGroupReference reference)

/-- Validate one single-star field shape and recover its authored group reference. -/
def SurfaceSingleStarFieldPath.groupReference
    (reference : SurfaceSingleStarFieldPath) : Except SingleGroupElabError SurfaceGroupPath := do
  if !reference.groupsBeforeStar.all (!·.isEmpty) || reference.starredGroup.isEmpty ||
      reference.field.isEmpty then
    let groupReference : SurfaceGroupPath :=
      { base := reference.base,
        groups := reference.groupsBeforeStar ++ [reference.starredGroup] }
    throw (.invalidGroupReference groupReference)
  match reference.base with
  | .relative parents =>
      if parents > 0 then throw (.wildcardWithParentNavigation parents)
  | .absolute => pure ()
  pure {
    base := reference.base
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
          formalCheck declaration.policy (raw.read row id)
        else
          malformedCheckedCell
    | .error _ => malformedCheckedCell

end A12Kernel
