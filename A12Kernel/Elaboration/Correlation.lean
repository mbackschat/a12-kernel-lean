import A12Kernel.Elaboration.SingleGroup
import A12Kernel.Elaboration.StarPath
import A12Kernel.Semantics.Correlation

/-! # A12Kernel.Elaboration.Correlation — checked lowering for repeatable filters

The established whole-rule route admits exactly one repeatable group, one starred direct-child Number field, an outer `FieldFilled` Number guard, and a correlated `Having` made from Number or `CurrentRepetition` comparisons and conjunction. The general-star route reuses the same authored filter traversal after a checked star path has fixed the complete candidate environment. It accepts only references available from that candidate environment or the captured rule environment and requires an ordinary reference to reach a reopened level.
-/

namespace A12Kernel

structure SurfaceHavingNumberRef where
  origin : HavingOrigin
  field : SurfaceFieldPath
  deriving Repr, DecidableEq

structure SurfaceHavingRepetitionRef where
  origin : HavingOrigin
  group : SurfaceGroupReference
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
  | wildcardOnRuleGroup
  | wildcardWithParentNavigation (parents : Nat)
  | fieldNotNumber (path : List String)
  | fieldOutsideGroup (origin : HavingOrigin)
      (fieldPath expectedGroup : List String)
  | fieldScopeMismatch (fieldPath : List String)
      (expected actual : List RepeatableLevel)
  | fieldOutsideEnvironment (origin : HavingOrigin) (fieldPath : List String)
      (available actual : List RepeatableLevel)
  | repetitionGroupMismatch (expected actual : GroupPath)
  | repetitionOutsideEnvironment (origin : HavingOrigin) (groupPath : GroupPath)
      (available : List RepeatableLevel) (actual : RepeatableLevel)
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

/-- Whether a resolved filter uses only leaves and conjunction, exactly the connective subset exposed by `SurfaceCorrelatedHaving`. -/
def CorrelatedHaving.isConjunctive (condition : CorrelatedHaving) : Bool :=
  match condition with
  | .leaf _ => true
  | .and left right =>
      CorrelatedHaving.isConjunctive left &&
        CorrelatedHaving.isConjunctive right
  | .or _ _ => false

/-- A resolved filter whose connective shape is in the image of the narrow authored surface. -/
structure ConjunctiveCorrelatedHaving where
  condition : CorrelatedHaving
  conjunctive : condition.isConjunctive = true

private def repeatableScopeAvailable :
    List RepeatableLevel → List RepeatableLevel → Bool
  | [], _ => true
  | _ :: _, [] => false
  | required :: requiredRest, available :: availableRest =>
      required == available &&
        repeatableScopeAvailable requiredRest availableRest

private def HavingOrigin.availableLevels (origin : HavingOrigin)
    (candidateLevels outerLevels : List RepeatableLevel) : List RepeatableLevel :=
  match origin with
  | .inner => candidateLevels
  | .outer => outerLevels

private def CorrelationElabError.ofSingleGroup (origin : HavingOrigin) :
    SingleGroupElabError → CorrelationElabError
  | .resolve error => .resolve error
  | .invalidGroupReference reference => .invalidGroupReference reference
  | .wildcardOnRuleGroup => .wildcardOnRuleGroup
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

private def resolveHavingRepetitionInGroup
    (declaringGroup : GroupPath) (group : RepeatableGroupDecl)
    (origin : HavingOrigin) (reference : SurfaceGroupReference) :
    Except CorrelationElabError HavingRepetitionRef := do
  let resolved ← reference.resolveAgainst declaringGroup |>.mapError (.ofSingleGroup origin)
  if resolved.path != group.path then
    throw (.repetitionGroupMismatch group.path resolved.path)
  pure { origin, level := group.level }

private def elaborateHavingCoreWith
    (resolveNumber : HavingOrigin → SurfaceFieldPath →
      Except CorrelationElabError ResolvedNumberRef)
    (resolveRepetition : HavingOrigin → SurfaceGroupReference →
      Except CorrelationElabError HavingRepetitionRef) :
    SurfaceCorrelatedHaving →
    Except CorrelationElabError ConjunctiveCorrelatedHaving
  | .compareNumbers op left right => do
      let coreOp ← match op.toCorrelation? with
        | some coreOp => pure coreOp
        | none => throw (.unsupportedOperator op)
      let leftResolved ← resolveNumber left.origin left.field
      let rightResolved ← resolveNumber right.origin right.field
      if !coreOp.acceptsScales leftResolved.core.field rightResolved.core.field then
        throw (.equalityScaleMismatch
          leftResolved.declaration.path leftResolved.core.field.info.scale
          rightResolved.declaration.path rightResolved.core.field.info.scale)
      pure {
        condition := .compareNumbers coreOp leftResolved.core rightResolved.core
        conjunctive := rfl }
  | .compareRepetitions op left right => do
      let coreOp ← match op.toCorrelation? with
        | some coreOp => pure coreOp
        | none => throw (.unsupportedOperator op)
      pure {
        condition := .compareRepetitions coreOp
          (← resolveRepetition left.origin left.group)
          (← resolveRepetition right.origin right.group)
        conjunctive := rfl }
  | .and left right => do
      let leftCore ← elaborateHavingCoreWith resolveNumber resolveRepetition left
      let rightCore ← elaborateHavingCoreWith resolveNumber resolveRepetition right
      pure {
        condition := .and leftCore.condition rightCore.condition
        conjunctive := by
          simp [CorrelatedHaving.isConjunctive, leftCore.conjunctive,
            rightCore.conjunctive] }

private def elaborateHavingCore (model : FlatModel) (declaringGroup : GroupPath)
    (group : RepeatableGroupDecl) (authored : SurfaceCorrelatedHaving) :
    Except CorrelationElabError CorrelatedHaving := do
  let checked ← elaborateHavingCoreWith
    (model.resolveHavingNumberInGroup declaringGroup group)
    (resolveHavingRepetitionInGroup declaringGroup group)
    authored
  pure checked.condition

private def FlatModel.resolveHavingNumberInEnvironment (model : FlatModel)
    (declaringGroup : GroupPath) (candidateLevels outerLevels : List RepeatableLevel)
    (origin : HavingOrigin) (reference : SurfaceFieldPath) :
    Except CorrelationElabError ResolvedNumberRef := do
  let declaration ←
    (model.resolveFieldDeclarationUnchecked declaringGroup reference).mapError .resolve
  let field ← match declaration.toNumberField? with
    | some field => pure field
    | none => throw (.fieldNotNumber declaration.path)
  let available := origin.availableLevels candidateLevels outerLevels
  if !repeatableScopeAvailable declaration.repeatableScope available then
    throw (.fieldOutsideEnvironment origin declaration.path available
      declaration.repeatableScope)
  pure { declaration, core := { origin, field } }

private def FlatModel.resolveHavingRepetitionInEnvironment (model : FlatModel)
    (declaringGroup : GroupPath) (candidateLevels outerLevels : List RepeatableLevel)
    (origin : HavingOrigin) (reference : SurfaceGroupReference) :
    Except CorrelationElabError HavingRepetitionRef := do
  let resolved ← reference.resolveAgainst declaringGroup |>.mapError (.ofSingleGroup origin)
  let group ← (model.lookupUniqueRepeatablePath resolved.path).mapError .resolve
  let available := origin.availableLevels candidateLevels outerLevels
  if !available.contains group.level then
    throw (.repetitionOutsideEnvironment origin group.path available group.level)
  pure { origin, level := group.level }

/-- Operator-specific static scale law for one filter leaf. Ordering is deliberately exempt. -/
def CorrelatedHavingLeaf.equalityScalesAgree : CorrelatedHavingLeaf → Bool
  | .compareNumbers op left right =>
      op.acceptsScales left.field right.field
  | .compareRepetitions _ _ _ => true

/-- Every leaf under the shared connective tree satisfies the static scale law. -/
def CorrelatedHaving.equalityScalesAgree (condition : CorrelatedHaving) : Bool :=
  condition.allLeaves CorrelatedHavingLeaf.equalityScalesAgree

def CorrelatedHavingLeaf.wellFormedForSingleGroup
    (model : FlatModel) (group : RepeatableGroupDecl) : CorrelatedHavingLeaf → Bool
  | .compareNumbers op left right =>
      model.admitsSingleGroupNumber group left.field &&
      model.admitsSingleGroupNumber group right.field &&
      op.acceptsScales left.field right.field
  | .compareRepetitions _ left right =>
      left.level == group.level && right.level == group.level

def CorrelatedHaving.wellFormedForSingleGroup (condition : CorrelatedHaving)
    (model : FlatModel) (group : RepeatableGroupDecl) : Bool :=
  condition.allLeaves fun leaf => leaf.wellFormedForSingleGroup model group

private def FlatModel.admitsHavingNumberInEnvironment (model : FlatModel)
    (candidateLevels outerLevels : List RepeatableLevel)
    (reference : HavingNumberRef) : Bool :=
  match model.lookupUniqueId reference.field.id with
  | .error _ => false
  | .ok declaration =>
      declaration.toNumberField? == some reference.field &&
        repeatableScopeAvailable declaration.repeatableScope
          (reference.origin.availableLevels candidateLevels outerLevels)

def CorrelatedHavingLeaf.wellFormedForEnvironments (model : FlatModel)
    (candidateLevels outerLevels : List RepeatableLevel) :
    CorrelatedHavingLeaf → Bool
  | .compareNumbers op left right =>
      model.admitsHavingNumberInEnvironment candidateLevels outerLevels left &&
        model.admitsHavingNumberInEnvironment candidateLevels outerLevels right &&
        op.acceptsScales left.field right.field
  | .compareRepetitions _ left right =>
      (left.origin.availableLevels candidateLevels outerLevels).contains left.level &&
        (right.origin.availableLevels candidateLevels outerLevels).contains right.level

/-- Static environment admission for a resolved filter tree. Candidate references must be available in every topology-produced candidate environment; `$` references must be available in the captured rule environment. -/
def CorrelatedHaving.wellFormedForEnvironments (condition : CorrelatedHaving)
    (model : FlatModel) (candidateLevels outerLevels : List RepeatableLevel) : Bool :=
  condition.allLeaves fun leaf =>
    leaf.wellFormedForEnvironments model candidateLevels outerLevels

private def HavingNumberRef.reachesReopenedLevel (reference : HavingNumberRef)
    (model : FlatModel) (reopenedLevels : List RepeatableLevel) : Bool :=
  match reference.origin, model.lookupUniqueId reference.field.id with
  | .inner, .ok declaration =>
      declaration.repeatableScope.any reopenedLevels.contains
  | _, _ => false

def CorrelatedHavingLeaf.reachesReopenedLevel (model : FlatModel)
    (reopenedLevels : List RepeatableLevel) : CorrelatedHavingLeaf → Bool
  | .compareNumbers _ left right =>
      left.reachesReopenedLevel model reopenedLevels ||
        right.reachesReopenedLevel model reopenedLevels
  | .compareRepetitions _ left right =>
      (left.origin == .inner && reopenedLevels.contains left.level) ||
        (right.origin == .inner && reopenedLevels.contains right.level)

/-- A legal star filter must depend on at least one unmarked reference at a level actually reopened by that starred operand. Bound-only or `$`-only trees do not establish an iteration to filter. -/
def CorrelatedHaving.reachesReopenedLevel (condition : CorrelatedHaving)
    (model : FlatModel) (reopenedLevels : List RepeatableLevel) : Bool :=
  condition.anyLeaf fun leaf => leaf.reachesReopenedLevel model reopenedLevels

/-- One filter resolved and certified against the exact candidate/captured environments of a checked star path. -/
structure CheckedStarHaving (model : FlatModel)
    (source : CheckedStarFieldPath model) (declaringGroup : GroupPath) where
  authored : ConjunctiveCorrelatedHaving
  wellFormed : authored.condition.wellFormedForEnvironments model
    (source.path.axes.map (·.level))
    (model.repeatableScopeForGroupPath declaringGroup) = true
  reachesReopenedLevel : authored.condition.reachesReopenedLevel model
    ((source.path.axes.map (·.level)).drop source.path.firstStar) = true

def CheckedStarHaving.condition
    (checked : CheckedStarHaving model source declaringGroup) :
    CorrelatedHaving :=
  checked.authored.condition

/-- Lower the source-closed Number/repetition-comparison filter fragment against one validated star plan. The result retains the shared filter tree and exact candidate/captured environment split; wider filter leaves remain outside this fragment. -/
def elaborateStarHavingCore (model : FlatModel) (declaringGroup : GroupPath)
    (source : CheckedStarFieldPath model) (authored : SurfaceCorrelatedHaving) :
    Except CorrelationElabError (CheckedStarHaving model source declaringGroup) := do
  let candidateLevels := source.path.axes.map (·.level)
  let reopenedLevels := candidateLevels.drop source.path.firstStar
  let outerLevels := model.repeatableScopeForGroupPath declaringGroup
  let checked ← elaborateHavingCoreWith
    (model.resolveHavingNumberInEnvironment declaringGroup candidateLevels outerLevels)
    (model.resolveHavingRepetitionInEnvironment declaringGroup candidateLevels outerLevels)
    authored
  let condition := checked.condition
  if hReopened : condition.reachesReopenedLevel model reopenedLevels = true then
    if hWellFormed :
        condition.wellFormedForEnvironments model candidateLevels outerLevels = true then
      pure {
        authored := checked
        wellFormed := hWellFormed
        reachesReopenedLevel := hReopened }
    else
      throw .incoherentCore
  else
    throw .missingInner

namespace CheckedStarFieldPath

/-- Apply one checked validation `Having` to topology-produced leaves before invoking the kind-specific cell classifier. Every filtered star consumer shares this order and the retained filter marker. -/
def selectedValidationHavingValueListSide (_checked : CheckedStarFieldPath model)
    (resolved : ResolvedStarTopology) (having : CorrelatedHaving)
    (filterRead : Env → FieldId → CheckedCell) (outer : Env)
    (classify : Env → ValueListCell kind) : ResolvedValueListSide kind :=
  let filterContext : CorrelationContext := { read := filterRead }
  let selected := having.selectEnvironments filterContext outer resolved.environments
  { cells := selected.map classify
    hasUninstantiatedTail := resolved.domain.hasOpenTail
    hasHaving := true }

/-- Resolve nested topology once, filter every candidate against its complete candidate/captured environments, and classify only retained leaves. -/
def resolvedValidationHavingValueListSide (checked : CheckedStarFieldPath model)
    (document : Document) (outer : Env) (having : CorrelatedHaving)
    (filterRead : Env → FieldId → CheckedCell)
    (classify : Env → ValueListCell kind) :
    Except StarAddressingError (ResolvedValueListSide kind) := do
  let resolved ← checked.path.resolve document outer
  pure (checked.selectedValidationHavingValueListSide resolved having filterRead outer classify)

/-- Dispatch one optional checked validation filter without duplicating the filter-before-classification branch in each scalar-kind adapter. -/
def resolvedOptionalValidationHavingValueListSide
    (checked : CheckedStarFieldPath model) (document : Document) (outer : Env)
    (filter : Option (CheckedStarHaving model checked declaringGroup))
    (filterRead : Env → FieldId → CheckedCell)
    (classify : Env → ValueListCell kind) :
    Except StarAddressingError (ResolvedValueListSide kind) :=
  match filter with
  | none => checked.resolvedValueListSide document outer classify
  | some having =>
      checked.resolvedValidationHavingValueListSide document outer
        having.condition filterRead classify

end CheckedStarFieldPath

/-- Partial validation skips a complete rule containing `Having` before topology or operand reads; otherwise it returns the evaluated value-list verdict. -/
inductive PartialHavingValueListResult where
  | skippedHaving
  | evaluated (verdict : Verdict)
  deriving Repr, DecidableEq

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
    rule.star.having.condition.isConjunctive &&
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
