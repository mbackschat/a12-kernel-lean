import A12Kernel.Elaboration.SingleGroup
import A12Kernel.Semantics.Correlation

/-! # A12Kernel.Elaboration.Correlation — checked lowering for one correlated star

This parser-independent capsule admits exactly one repeatable group, one starred direct-child Number field, an outer `FieldFilled` Number guard, and a correlated `Having` made from Number or `CurrentRepetition` comparisons and conjunction. It resolves authored paths against an expanded model before erasing them into the existing correlation core.
-/

namespace A12Kernel

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

private def CorrelationElabError.ofSingleGroup (origin : HavingOrigin) :
    SingleGroupElabError → CorrelationElabError
  | .resolve error => .resolve error
  | .invalidGroupReference reference => .invalidGroupReference reference
  | .wildcardWithParentNavigation parents => .wildcardWithParentNavigation parents
  | .fieldNotNumber path => .fieldNotNumber path
  | .fieldOutsideGroup fieldPath expectedGroup =>
      .fieldOutsideGroup origin fieldPath expectedGroup
  | .fieldScopeMismatch fieldPath expected actual =>
      .fieldScopeMismatch fieldPath expected actual

private def FlatModel.resolveHavingNumberInGroup (model : FlatModel)
    (declaringGroup : GroupPath) (group : RepeatableGroupDecl)
    (origin : HavingOrigin) (reference : SurfaceFieldPath) :
    Except CorrelationElabError ResolvedNumberRef := do
  let (declaration, field) ← model.resolveNumberInGroup declaringGroup group reference
    |>.mapError (.ofSingleGroup origin)
  pure { declaration, core := { origin, field } }

private def elaborateHavingCore (model : FlatModel) (declaringGroup : GroupPath)
    (group : RepeatableGroupDecl) : SurfaceCorrelatedHaving →
    Except CorrelationElabError CorrelatedHaving
  | .compareNumbers op left right => do
      let coreOp ← match op.toCorrelation? with
        | some coreOp => pure coreOp
        | none => throw (.unsupportedOperator op)
      let leftResolved ← model.resolveHavingNumberInGroup declaringGroup group left.origin left.field
      let rightResolved ← model.resolveHavingNumberInGroup declaringGroup group right.origin right.field
      if !coreOp.acceptsScales leftResolved.core.field rightResolved.core.field then
        throw (.equalityScaleMismatch
          leftResolved.declaration.path leftResolved.core.field.info.scale
          rightResolved.declaration.path rightResolved.core.field.info.scale)
      pure (.compareNumbers coreOp leftResolved.core rightResolved.core)
  | .compareRepetitions op left right => do
      let coreOp ← match op.toCorrelation? with
        | some coreOp => pure coreOp
        | none => throw (.unsupportedOperator op)
      let leftGroup ← left.group.resolveAgainst declaringGroup |>.mapError (.ofSingleGroup left.origin)
      if leftGroup != group.path then
        throw (.repetitionGroupMismatch group.path leftGroup)
      let rightGroup ← right.group.resolveAgainst declaringGroup |>.mapError (.ofSingleGroup right.origin)
      if rightGroup != group.path then
        throw (.repetitionGroupMismatch group.path rightGroup)
      pure (.compareRepetitions coreOp
        { origin := left.origin, level := group.level }
        { origin := right.origin, level := group.level })
  | .and left right => do
      pure (.and (← elaborateHavingCore model declaringGroup group left)
        (← elaborateHavingCore model declaringGroup group right))

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
  | .compareRepetitions _ left right =>
      left.level == group.level && right.level == group.level
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
      let groupReference ← rule.valueField.groupReference |>.mapError (.ofSingleGroup .inner)
      let groupPath ← groupReference.resolveAgainst declaringGroup |>.mapError (.ofSingleGroup .inner)
      let group ← (model.lookupUniqueRepeatablePath groupPath).mapError .resolve
      let valueReference : SurfaceFieldPath :=
        { base := .absolute, groups := group.path, field := rule.valueField.field }
      let (_, valueField) ←
        model.resolveNumberInGroup declaringGroup group valueReference |>.mapError (.ofSingleGroup .inner)
      let (errorDeclaration, errorField) ←
        model.resolveNumberInGroup declaringGroup group rule.errorField |>.mapError (.ofSingleGroup .inner)
      let (guardDeclaration, guardField) ←
        model.resolveNumberInGroup declaringGroup group rule.guardField |>.mapError (.ofSingleGroup .inner)
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

def CheckedSingleCorrelatedRule.firingRows
    (checked : CheckedSingleCorrelatedRule model) (raw : RawSingleGroupContext) :
    Except SingleGroupContextError (List RowIndex) := do
  raw.validate
  pure <| checked.core.star.firingRowsOn checked.core.guardField
    (model.checkSingleGroupContext checked.core.group raw)

end A12Kernel
