import A12Kernel.Elaboration.Flat
import A12Kernel.Semantics.Correlation

/-! # A12Kernel.Elaboration.Correlation — checked lowering for one correlated star

This parser-independent capsule admits exactly one repeatable group, one starred direct-child Number field, an outer `FieldFilled` Number guard, and a correlated `Having` made from Number or `CurrentRepetition` comparisons and conjunction. It resolves authored paths against an expanded model before erasing them into the existing correlation core.
-/

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

structure SurfaceHavingNumberRef where
  origin : HavingOrigin
  field : SurfaceFieldPath
  deriving Repr, DecidableEq

structure SurfaceHavingRepetitionRef where
  origin : HavingOrigin
  group : SurfaceGroupPath
  deriving Repr, DecidableEq

inductive SurfaceCorrelatedHaving where
  | compareNumbers (op : SurfaceComparisonOp)
      (left right : SurfaceHavingNumberRef)
  | compareRepetitions (op : SurfaceComparisonOp)
      (left right : SurfaceHavingRepetitionRef)
  | and (left right : SurfaceCorrelatedHaving)
  deriving Repr, DecidableEq

/-- The exact admitted validation shape: the error target is the outer Number guard, and the starred consumer is filtered by a genuinely correlated `Having`. Requiring `errorField = guardField` is this capsule's routing boundary, not a claim that every kernel rule has that shape. -/
structure SurfaceSingleCorrelatedRule where
  errorField : SurfaceFieldPath
  guardField : SurfaceFieldPath
  valueField : SurfaceSingleStarFieldPath
  having : SurfaceCorrelatedHaving
  deriving Repr, DecidableEq

inductive CorrelationElabError where
  | resolve (error : ResolveError)
  | invalidGroupReference (reference : SurfaceGroupPath)
  | wildcardWithParentNavigation (parents : Nat)
  | fieldNotNumber (path : List String)
  | fieldOutsideGroup (origin : HavingOrigin)
      (fieldPath expectedGroup : List String)
  | fieldScopeMismatch (fieldPath : List String)
      (expected actual : List RepeatableLevel)
  | repetitionGroupMismatch (expected actual : GroupPath)
  | equalityScaleMismatch (leftPath : List String) (leftScale : Nat)
      (rightPath : List String) (rightScale : Nat)
  | unsupportedOperator (op : SurfaceComparisonOp)
  | missingInner
  | missingOuter
  | errorGuardMismatch (errorPath guardPath : List String)
  | incoherentCore
  deriving Repr, DecidableEq

private def SurfaceGroupPath.resolveAgainst (reference : SurfaceGroupPath)
    (declaringGroup : GroupPath) : Except CorrelationElabError GroupPath := do
  if !GroupPath.isValid declaringGroup then
    throw (.resolve (.invalidRuleGroup declaringGroup))
  if !reference.groups.all (!·.isEmpty) then
    throw (.invalidGroupReference reference)
  let path ← match reference.base with
    | .absolute => pure reference.groups
    | .relative parents =>
        pure ((← GroupPath.walkUp declaringGroup parents |>.mapError .resolve) ++ reference.groups)
  if GroupPath.isValid path then pure path else throw (.invalidGroupReference reference)

private def SurfaceSingleStarFieldPath.groupReference
    (reference : SurfaceSingleStarFieldPath) : Except CorrelationElabError SurfaceGroupPath := do
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
  let groupReference : SurfaceGroupPath :=
    { base := reference.base,
      groups := reference.groupsBeforeStar ++ [reference.starredGroup] }
  pure groupReference

private def SurfaceComparisonOp.toCorrelation? : SurfaceComparisonOp →
    Option CorrelationComparisonOp
  | .equal => some .equal
  | .notEqual => some .notEqual
  | .less => some .lessThan
  | _ => none

def CorrelationComparisonOp.acceptsScales (op : CorrelationComparisonOp)
    (left right : FlatNumberField) : Bool :=
  match op with
  | .equal | .notEqual => left.info.scale == right.info.scale
  | .lessThan => true

private structure ResolvedNumberRef where
  declaration : FlatFieldDecl
  core : HavingNumberRef

private def FlatModel.resolveNumberInGroup (model : FlatModel)
    (declaringGroup : GroupPath) (group : RepeatableGroupDecl)
    (origin : HavingOrigin) (reference : SurfaceFieldPath) :
    Except CorrelationElabError ResolvedNumberRef := do
  let declaration ←
    (model.resolveFieldDeclarationUnchecked declaringGroup reference).mapError .resolve
  if declaration.groupPath != group.path then
    throw (.fieldOutsideGroup origin declaration.path group.path)
  let expectedScope := [group.level]
  if declaration.repeatableScope != expectedScope then
    throw (.fieldScopeMismatch declaration.path expectedScope declaration.repeatableScope)
  let field ← match declaration.toNumberField? with
    | some field => pure field
    | none => throw (.fieldNotNumber declaration.path)
  pure { declaration, core := { origin, field } }

private def FlatModel.resolveNumberFieldInGroup (model : FlatModel)
    (declaringGroup : GroupPath) (group : RepeatableGroupDecl)
    (reference : SurfaceFieldPath) :
    Except CorrelationElabError (FlatFieldDecl × FlatNumberField) := do
  let resolved ← model.resolveNumberInGroup declaringGroup group .inner reference
  pure (resolved.declaration, resolved.core.field)

private def elaborateHavingCore (model : FlatModel) (declaringGroup : GroupPath)
    (group : RepeatableGroupDecl) : SurfaceCorrelatedHaving →
    Except CorrelationElabError CorrelatedHaving
  | .compareNumbers op left right => do
      let coreOp ← match op.toCorrelation? with
        | some coreOp => pure coreOp
        | none => throw (.unsupportedOperator op)
      let leftResolved ← model.resolveNumberInGroup declaringGroup group left.origin left.field
      let rightResolved ← model.resolveNumberInGroup declaringGroup group right.origin right.field
      if !coreOp.acceptsScales leftResolved.core.field rightResolved.core.field then
        throw (.equalityScaleMismatch
          leftResolved.declaration.path leftResolved.core.field.info.scale
          rightResolved.declaration.path rightResolved.core.field.info.scale)
      pure (.compareNumbers coreOp leftResolved.core rightResolved.core)
  | .compareRepetitions op left right => do
      let coreOp ← match op.toCorrelation? with
        | some coreOp => pure coreOp
        | none => throw (.unsupportedOperator op)
      let leftGroup ← left.group.resolveAgainst declaringGroup
      if leftGroup != group.path then
        throw (.repetitionGroupMismatch group.path leftGroup)
      let rightGroup ← right.group.resolveAgainst declaringGroup
      if rightGroup != group.path then
        throw (.repetitionGroupMismatch group.path rightGroup)
      pure (.compareRepetitions coreOp left.origin right.origin)
  | .and left right => do
      pure (.and (← elaborateHavingCore model declaringGroup group left)
        (← elaborateHavingCore model declaringGroup group right))

/-- A Number field is admitted only when its unique declaration is a direct child of the exact repeatable group, carries exactly that singleton scope, and has identical numeric metadata. -/
def FlatModel.admitsSingleGroupNumber (model : FlatModel)
    (group : RepeatableGroupDecl) (field : FlatNumberField) : Bool :=
  match model.lookupUniqueId field.id with
  | .error _ => false
  | .ok declaration =>
      declaration.groupPath == group.path &&
      declaration.repeatableScope == [group.level] &&
      (FlatField.number field).matchesDecl declaration

/-- Operator-specific static scale law. Ordering is deliberately exempt. -/
def CorrelatedHaving.equalityScalesAgree : CorrelatedHaving → Bool
  | .compareNumbers op left right =>
      op.acceptsScales left.field right.field
  | .compareRepetitions _ _ _ => true
  | .and left right => left.equalityScalesAgree && right.equalityScalesAgree

def CorrelatedHaving.wellFormedForSingleGroup (condition : CorrelatedHaving)
    (model : FlatModel) (group : RepeatableGroupDecl) : Bool :=
  match condition with
  | .compareNumbers op left right =>
      model.admitsSingleGroupNumber group left.field &&
      model.admitsSingleGroupNumber group right.field &&
      op.acceptsScales left.field right.field
  | .compareRepetitions _ _ _ => true
  | .and left right =>
      left.wellFormedForSingleGroup model group &&
      right.wellFormedForSingleGroup model group

structure ResolvedSingleCorrelatedRule where
  group : RepeatableGroupDecl
  errorField : FlatNumberField
  guardField : FlatNumberField
  star : SingleCorrelatedStar

def ResolvedSingleCorrelatedRule.wellFormedBool
    (rule : ResolvedSingleCorrelatedRule) (model : FlatModel) : Bool :=
  model.repeatableGroups.contains rule.group &&
    model.admitsSingleGroupNumber rule.group rule.errorField &&
    model.admitsSingleGroupNumber rule.group rule.guardField &&
    rule.errorField == rule.guardField &&
    model.admitsSingleGroupNumber rule.group rule.star.valueField &&
    rule.star.having.condition.wellFormedForSingleGroup model rule.group

def ResolvedSingleCorrelatedRule.WellFormed
    (rule : ResolvedSingleCorrelatedRule) (model : FlatModel) : Prop :=
  rule.wellFormedBool model = true

/-- The only repeatable surface-to-core result accepted by the checked runtime route. -/
structure CheckedSingleCorrelatedRule (model : FlatModel) where
  core : ResolvedSingleCorrelatedRule
  modelWellFormed : model.validate.isOk = true
  wellFormed : core.WellFormed model

/-- Checked lowering for the exact one-star correlated validation fragment. All-inner `Having` is rejected as a routing boundary to the earlier uncorrelated capsule; it is not classified as kernel-invalid here. -/
def elaborateSingleCorrelatedRule (model : FlatModel) (declaringGroup : GroupPath)
    (rule : SurfaceSingleCorrelatedRule) :
    Except CorrelationElabError (CheckedSingleCorrelatedRule model) :=
  match hModel : model.validate with
  | .error error => .error (.resolve error)
  | .ok () => do
      let groupReference ← rule.valueField.groupReference
      let groupPath ← groupReference.resolveAgainst declaringGroup
      let group ← (model.lookupUniqueRepeatablePath groupPath).mapError .resolve
      let valueReference : SurfaceFieldPath :=
        { base := .absolute, groups := group.path, field := rule.valueField.field }
      let (_, valueField) ←
        model.resolveNumberFieldInGroup declaringGroup group valueReference
      let (errorDeclaration, errorField) ←
        model.resolveNumberFieldInGroup declaringGroup group rule.errorField
      let (guardDeclaration, guardField) ←
        model.resolveNumberFieldInGroup declaringGroup group rule.guardField
      if errorField != guardField then
        throw (.errorGuardMismatch errorDeclaration.path guardDeclaration.path)
      let condition ← elaborateHavingCore model declaringGroup group rule.having
      let having ← match condition.check with
        | .ok checked => pure checked
        | .error .missingInner => throw .missingInner
        | .error .missingOuter => throw .missingOuter
      let core : ResolvedSingleCorrelatedRule :=
        { group, errorField, guardField, star := { valueField, having } }
      if hCore : core.wellFormedBool model = true then
        pure {
          core
          modelWellFormed := by
            rw [hModel]
            rfl
          wellFormed := hCore
        }
      else
        throw .incoherentCore

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

def CheckedSingleCorrelatedRule.firingRows
    (checked : CheckedSingleCorrelatedRule model) (raw : RawSingleGroupContext) :
    Except SingleGroupContextError (List RowIndex) := do
  raw.validate
  pure <| checked.core.star.firingRowsOn checked.core.guardField
    (model.checkSingleGroupContext checked.core.group raw)

end A12Kernel
