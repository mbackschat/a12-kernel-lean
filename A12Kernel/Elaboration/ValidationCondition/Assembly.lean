import A12Kernel.Elaboration.ValidationCondition.Iteration

/-! # Checked validation-condition assembly -/

namespace A12Kernel

inductive ValidationConditionAssemblyError where
  | invalidModel (error : ResolveError)
  | groupReference (error : FixedGroupReferenceError)
  | fieldReference (error : ResolveError)
  | starredGroup (error : StarredGroupElabError)
  | starredGroupNotAllowed (operator : GroupFillQuantifier)
  | repeatableFieldRequired (path : List String)
  | emptyGroupList
  | groupListNeedsMultipleOperands
  | rootGroupInGroupList (path : GroupPath)
  | rootGroupRequiresSoleOperand (path : GroupPath)
  | overlappingGroupListOperands (left right : List String)
  | rowGroupMismatch (left right : GroupPath)
  | declaringGroupMismatch (left right : GroupPath)
  | repetitionNotUnique (error : RepetitionNotUniqueElabError)
  | iteratedDateRange (error : IteratedDateRangeConditionElabError)
  | multipleRepetitionNotUnique
  | stringPattern (error : StringPatternConditionElabError)
  | constructedDate (error : ConstructedDateComponentsElabError)
  | incoherentCore
  deriving Repr, DecidableEq

/-- A mixed resolved tree with separate lexical origin and certified row binding. The error field
may bind a descendant scope without relocating the declaration (spec/07 §1 and spec/08 §2). -/
structure CheckedValidationCondition (model : FlatModel) where
  rowGroup : GroupPath
  declaringGroup : GroupPath := rowGroup
  core : ValidationCondition model
  modelWellFormed : model.validate.isOk = true
  wellFormed : core.wellFormedBool rowGroup = true

private def ValidationConditionAssemblyError.ofCurrentRepetitionSourceError :
    CurrentRepetitionSourceElabError → ValidationConditionAssemblyError
  | .model error => .invalidModel error
  | .reference error => .groupReference (.reference error)
  | .group error => .groupReference (.reference (.resolve error))

namespace ValidationConditionAssemblyError

/-- Project the measured group-list quantifier admission classes. Every other refusal returns `none`, which keeps the uncovered surface countable.

    The exact-duplicate and ancestor-overlap classes are **two** Kernel classes, and one local error covers both, retaining both paths so the split is read off the data. Root-family classes are distinct and are reached only after strict overlap has had the chance to pre-empt them. -/
def groupListDiagnostic? :
    ValidationConditionAssemblyError → Option KernelStaticDiagnostic
  | .groupListNeedsMultipleOperands => some .paramSizeInvalid2
  | .overlappingGroupListOperands left right =>
      some (if left == right then .duplicateParam1 else .duplicateParam2)
  | .rootGroupInGroupList _ => some .rootGroupReferenced
  | .rootGroupRequiresSoleOperand _ => some .rootGroupWithOtherParameters
  | .starredGroupNotAllowed _ => some .noWildcardsGAllowed
  -- The operand's own resolution owns these classes: a miss draws the class of the segment that
  -- missed, as a field operand does
  -- ([checkpoint](../../../docs/sources/path-resolution-class-probes.md#src-group-operand-resolution-classes)).
  | .groupReference error => error.diagnostic?
  -- Operands are read before every list gate, so an empty starred group answers ahead of the star
  -- gate and arity under all five quantifiers
  -- ([checkpoint](../../../docs/sources/static-admission-and-class-probes.md#src-entity-list-kind-empty-and-root-carriers)).
  | .starredGroup error => error.diagnostic?
  | .fieldReference error => error.diagnostic?
  -- Named rather than wildcarded, so a new refusal must be classified rather than absorbed. None of
  -- these is measured as its own class through this projection.
  | .invalidModel _ | .repeatableFieldRequired _ | .emptyGroupList | .rowGroupMismatch _ _
  | .declaringGroupMismatch _ _
  | .repetitionNotUnique _ | .iteratedDateRange _ | .multipleRepetitionNotUnique
  | .constructedDate _ | .stringPattern _ | .incoherentCore => none

end ValidationConditionAssemblyError

namespace CheckedValidationCondition

/-- Public checked-tree query used by Kernel 30.8.1 partial-validation consumers before relevance or execution. -/
def hasHaving (condition : CheckedValidationCondition model) : Bool :=
  condition.core.hasHaving

/-- Certify a resolved mixed core once after a semantic desugaring has assembled its complete tree. -/
def checkCore (model : FlatModel) (rowGroup : GroupPath)
    (core : ValidationCondition model) (modelWellFormed : model.validate.isOk = true)
    (declaringGroup : GroupPath := rowGroup) :
    Except ValidationConditionAssemblyError (CheckedValidationCondition model) :=
  if hCore : core.wellFormedBool rowGroup = true then
    .ok { rowGroup, declaringGroup, core, modelWellFormed, wellFormed := hCore }
  else
    .error .incoherentCore

/-- Recheck an existing core at an error-field binding while preserving lexical origin. A leaf
whose certificate depends on its original group is refused rather than silently reinterpreted. -/
def atBinding (condition : CheckedValidationCondition model) (rowGroup : GroupPath) :
    Except ValidationConditionAssemblyError (CheckedValidationCondition model) :=
  checkCore model rowGroup condition.core condition.modelWellFormed condition.declaringGroup

/-- Lift a checked flat tree without nesting or changing its connective shape. -/
def fromFlat (condition : CheckedFlatCondition model) :
    Except ValidationConditionAssemblyError (CheckedValidationCondition model) :=
  checkCore model condition.rowGroup (ValidationCondition.flat condition.core)
    condition.modelWellFormed

/-- Compose either constructed-Date validity projection using the existing component certificate. -/
def fromConstructedDateValidity (model : FlatModel) (rowGroup : GroupPath)
    (operation : ConstructedDateValidityOp) (surface : SurfaceConstructedDateComponents) :
    Except ValidationConditionAssemblyError (CheckedValidationCondition model) := do
  match hModel : model.validate with
  | .error error => throw (.invalidModel error)
  | .ok () =>
      let source ← (elaborateConstructedDateSources model surface).mapError .constructedDate
      checkCore model rowGroup (.leaf (.constructedDateValidity operation source))
        (by rw [hModel]; rfl)

/-- Assemble one explicit `Valid`/`Invalid` predicate at a rule group.

    The model check runs first, as it does for every member, and `checkCore` then applies the leaf's own well-formedness — which for this family is the nonrepeatable operand. Both refusals of the leaf itself are mapped to the assembly's generic incoherent-core class rather than to a Kernel diagnostic, because no row places a class on either at this position. -/
def fromCustomFieldValidity (model : FlatModel) (rowGroup : GroupPath)
    (world : World) (source : FieldId) (name : String)
    (operation : CustomFieldValidityOp) :
    Except ValidationConditionAssemblyError (CheckedValidationCondition model) :=
  match hModel : model.validate with
  | .error error => .error (.invalidModel error)
  | .ok () =>
      match elaborateCustomFieldValidityLeaf model world source name operation with
      | .error _ => .error .incoherentCore
      | .ok leaf =>
          checkCore model rowGroup (ValidationCondition.customFieldValidity leaf)
            (by rw [hModel]; rfl)

/-- Assemble one `PatternMatched`/`PatternViolated` leaf at a rule group, keeping the compiler that
    admitted its pattern beside the checked condition. -/
def fromStringPattern (model : FlatModel) (rowGroup : GroupPath)
    (compilePattern : StringPatternCompiler) (surface : SurfaceStringPatternCondition) :
    Except ValidationConditionAssemblyError (CheckedValidationCondition model) :=
  match hModel : model.validate with
  | .error error => .error (.invalidModel error)
  | .ok () => do
      let condition ← (elaborateStringPatternCondition compilePattern model rowGroup surface).mapError
        .stringPattern
      checkCore model rowGroup (.leaf (.stringPattern { compilePattern, condition }))
        (by rw [hModel]; rfl)

/-- Join the source-owning token comparison to ordinary condition composition. -/
def fromTokenComparison (rowGroup : GroupPath) (comparison : CheckedTokenComparison model) :
    Except ValidationConditionAssemblyError (CheckedValidationCondition model) :=
  checkCore model rowGroup (.leaf (.tokenComparison comparison)) comparison.modelWellFormed

/-- Join String expressions to the shared condition tree; whole-rule execution owns
its full-validation iteration domain independently of the expression's operator. -/
def fromStringExpression (rowGroup : GroupPath) (comparison : CheckedStringExpressionComparison model) :
    Except ValidationConditionAssemblyError (CheckedValidationCondition model) :=
  checkCore model rowGroup (.leaf (.stringExpression comparison)) comparison.left.modelWellFormed

/-- Join a sealed scalar temporal comparison to the existing connective tree. -/
def fromScalarTemporal (rowGroup : GroupPath) (comparison : CheckedScalarTemporalComparison model)
    (declaringGroup : GroupPath := rowGroup) :
    Except ValidationConditionAssemblyError (CheckedValidationCondition model) :=
  checkCore model rowGroup (.leaf (.scalarTemporal comparison)) comparison.modelWellFormed declaringGroup

/-- Compose the owning uniqueness certificate without changing its operand order or identity. -/
def fromValuesNotUnique (rowGroup : GroupPath) (source : CheckedValuesNotUniqueCondition model) :
    Except ValidationConditionAssemblyError (CheckedValidationCondition model) :=
  checkCore model rowGroup (.leaf (.valuesNotUnique source)) source.modelWellFormed

/-- Compose a value-list certificate without flattening its authored operands. -/
def fromValueList (rowGroup : GroupPath) (source : CheckedValueListCondition model) :
    Except ValidationConditionAssemblyError (CheckedValidationCondition model) :=
  checkCore model rowGroup (.leaf (.valueList source)) source.modelWellFormed

/-- Lift one checked numeric comparison at its certified rule-instance group. -/
def fromNumeric (comparison : CheckedNumericComparison model) :
    Except ValidationConditionAssemblyError (CheckedValidationCondition model) :=
  checkCore model comparison.rowGroup
    (ValidationCondition.numericIn comparison.operandScope comparison.core)
    comparison.modelWellFormed

/-- Lift one checked ordered-numeric comparison without reconstructing or flattening its authored expression tree. -/
def fromOrderedNumeric
    (comparison : CheckedOrderedNumericComparison model)
    (declaringGroup : GroupPath := comparison.rowGroup) :
    Except ValidationConditionAssemblyError (CheckedValidationCondition model) :=
  checkCore model comparison.rowGroup
    (ValidationCondition.orderedNumericIn
      comparison.operandScope comparison.core)
    comparison.modelWellFormed declaringGroup

  /-- Resolve and certify one group-presence predicate against the same model and declaring group used by the surrounding rule. Repeatable ancestry is retained for the addressed whole-rule route rather than rejected as a fixed-list operand. -/
def fromGroupPresence (model : FlatModel) (rowGroup : GroupPath)
    (reference : SurfaceGroupReference) (operator : GroupPresenceOperator) :
    Except ValidationConditionAssemblyError (CheckedValidationCondition model) :=
  match hModel : model.validate with
  | .error error => .error (.invalidModel error)
  | .ok () => do
      let resolved ← reference.resolveAgainst rowGroup
        |>.mapError (.groupReference ∘ .reference)
      if !model.hasGroupPath resolved.path then
        throw (.groupReference (model.unknownGroupError resolved.path))
      checkCore model rowGroup
        (ValidationCondition.groupPresence operator resolved)
        (by rw [hModel]; rfl)

/-- Resolve one ordinary non-starred repeatable field presence reference. The declaration itself is the checked source; no wildcard topology or caller-supplied environment is manufactured here. -/
def fromRepeatableFieldPresence (model : FlatModel) (rowGroup : GroupPath)
    (operator : RepeatableFieldPresenceOperator)
    (reference : SurfaceFieldPath) (writtenGroup : GroupPath := rowGroup) :
    Except ValidationConditionAssemblyError
      (CheckedValidationCondition model) :=
  match hModel : model.validate with
  | .error error => .error (.invalidModel error)
  | .ok () => do
      let declaration ←
        (model.resolvePresenceOperand rowGroup writtenGroup reference
          (model.resolveFieldDeclarationUnchecked rowGroup reference))
          |>.mapError .fieldReference
      if declaration.repeatableScope.isEmpty then
        throw (.repeatableFieldRequired declaration.path)
      checkCore model rowGroup
        (ValidationCondition.repeatableFieldPresence operator declaration)
        (by rw [hModel]; rfl)

/-- Resolve one DateRange condition whose operands the rule's own iteration may cross. The reading
scope is the rule group's, so the locus decides admission exactly as the Kernel's does, and an
operand crossing an unbound level is refused as a repeatable reference. A condition whose operands
are all scalar is admitted too and simply derives no iteration, because this leaf is the family's
only rule-level owner.

The resolved operand paths are supplied by each member's own front end; this shared step owns only
the locus scope and the checked-core certification. -/
private def fromIteratedDateRange (model : FlatModel) (rowGroup : GroupPath)
    (build : List RepeatableLevel →
      Except IteratedDateRangeConditionElabError
        (IteratedDateRangeCondition model)) :
    Except ValidationConditionAssemblyError
      (CheckedValidationCondition model) :=
  match hModel : model.validate with
  | .error error => .error (.invalidModel error)
  | .ok () => do
      let condition ←
        (build (model.repeatableScopeForGroupPath rowGroup)).mapError fun
          -- Every member reports a locus refusal as the same resolution failure, so a consumer
          -- reads one class for "this operand crosses a level the rule does not iterate" rather
          -- than one per carrier.
          | .storedEquality (.left (.source error))
          | .storedEquality (.right (.source error))
          | .operand (.source error)
          | .yearlessOperand (.source (.source error))
          | .storedOperand (.source error)
          | .construction (.start (.targetPolicy (.resolve error)))
          | .construction (.finish (.targetPolicy (.resolve error)))
          | .constructionPair (.left (.start (.targetPolicy (.resolve error))))
          | .constructionPair (.left (.finish (.targetPolicy (.resolve error))))
          | .constructionPair (.right (.start (.targetPolicy (.resolve error))))
          | .constructionPair (.right (.finish (.targetPolicy (.resolve error))))
          | .overlap (.shape (.resolve error))
          | .pluralOverlap (.shape (.resolve error))
          | .yearlessOverlap (.source (.shape (.resolve error))) =>
              .fieldReference error
          | error => .iteratedDateRange error
      checkCore model rowGroup (.leaf (.iteratedDateRange condition))
        (by rw [hModel]; rfl)

/-- Resolve two authored field references at the rule group without deciding their repetition. -/
private def resolveIteratedOperand (model : FlatModel) (rowGroup : GroupPath)
    (reference : SurfaceFieldPath) :
    Except ValidationConditionAssemblyError FlatFieldDecl :=
  (model.resolveFieldDeclarationUnchecked rowGroup reference)
    |>.mapError .fieldReference

/-- Resolve a stored DateRange comparison side, a field-value read whose gates answer ahead of the
    comparison's own, measured on the stored-against-stored equality
    ([checkpoint](../../../docs/sources/static-admission-and-class-probes.md#src-field-value-read-remaining-sites))
    and carried to a constructed range's stored partner by assumption. A constructed range's
    endpoints are entity arguments and keep `resolveIteratedOperand`. -/
private def resolveIteratedFieldValueRead (model : FlatModel) (rowGroup : GroupPath)
    (reference : SurfaceFieldPath) :
    Except ValidationConditionAssemblyError FlatFieldDecl :=
  (checkFieldValueRead (model.resolveFieldDeclarationUnchecked rowGroup reference)
    (model.ruleGroupRead rowGroup rowGroup reference)).mapError .fieldReference

/-- One stored-versus-stored DateRange equality read at the rule's own row. -/
def fromIteratedDateRangeEquality (model : FlatModel) (rowGroup : GroupPath)
    (comparison : EqualityOp) (left right : SurfaceFieldPath) :
    Except ValidationConditionAssemblyError
      (CheckedValidationCondition model) := do
  let leftDeclaration ← resolveIteratedFieldValueRead model rowGroup left
  let rightDeclaration ← resolveIteratedFieldValueRead model rowGroup right
  fromIteratedDateRange model rowGroup fun scope =>
    elaborateIteratedStoredEquality model scope leftDeclaration.id
      rightDeclaration.id comparison

/-- One selected DateRange endpoint compared with a fixed complete date at the rule's own row. -/
def fromIteratedDateRangeBoundAgainstFixed (model : FlatModel)
    (rowGroup : GroupPath) (source : SurfaceFieldPath)
    (bound : DateRangeBound) (position : DateRangeBoundComparisonPosition)
    (comparison : TemporalComparisonOp) (expected : FullDate) :
    Except ValidationConditionAssemblyError
      (CheckedValidationCondition model) := do
  let declaration ← resolveIteratedOperand model rowGroup source
  fromIteratedDateRange model rowGroup fun scope =>
    elaborateIteratedBoundAgainstFixed model scope declaration.id bound
      position comparison expected

/-- Two selected DateRange endpoints compared with each other at the rule's own row. -/
def fromIteratedDateRangeBoundPair (model : FlatModel) (rowGroup : GroupPath)
    (left : SurfaceFieldPath) (leftBound : DateRangeBound)
    (right : SurfaceFieldPath) (rightBound : DateRangeBound)
    (comparison : TemporalComparisonOp) :
    Except ValidationConditionAssemblyError
      (CheckedValidationCondition model) := do
  let leftDeclaration ← resolveIteratedOperand model rowGroup left
  let rightDeclaration ← resolveIteratedOperand model rowGroup right
  fromIteratedDateRange model rowGroup fun scope =>
    elaborateIteratedBoundPair model scope leftDeclaration.id leftBound
      rightDeclaration.id rightBound comparison

/-- One unconfigured yearless plural DateRange overlap predicate read at the rule's own row. -/
def fromIteratedYearlessDateRangePluralOverlap (model : FlatModel)
    (rowGroup : GroupPath)
    (authored : SurfaceAtLeastOneDateRangeOverlapsSource) (writtenGroup : GroupPath := rowGroup) :
    Except ValidationConditionAssemblyError
      (CheckedValidationCondition model) :=
  fromIteratedDateRange model rowGroup fun scope =>
    elaborateIteratedYearlessPluralOverlap model rowGroup scope authored writtenGroup

/-- One unconfigured yearless DateRange overlap predicate read at the rule's own row. -/
def fromIteratedYearlessDateRangeOverlap (model : FlatModel)
    (rowGroup : GroupPath) (authored : SurfaceFieldEntitySource) (writtenGroup : GroupPath := rowGroup) :
    Except ValidationConditionAssemblyError
      (CheckedValidationCondition model) :=
  fromIteratedDateRange model rowGroup fun scope =>
    elaborateIteratedYearlessOverlap model rowGroup scope authored writtenGroup

/-- One plural DateRange overlap predicate read at the rule's own row. -/
def fromIteratedDateRangePluralOverlap (model : FlatModel)
    (rowGroup : GroupPath)
    (authored : SurfaceAtLeastOneDateRangeOverlapsSource) (writtenGroup : GroupPath := rowGroup) :
    Except ValidationConditionAssemblyError
      (CheckedValidationCondition model) :=
  fromIteratedDateRange model rowGroup fun scope =>
    elaborateIteratedPluralOverlap model rowGroup scope authored writtenGroup

/-- One constructed range compared with another at the rule's own row. -/
def fromIteratedDateRangeConstructionPair (model : FlatModel)
    (rowGroup : GroupPath)
    (leftStart leftFinish rightStart rightFinish : SurfaceFieldPath)
    (comparison : EqualityOp) :
    Except ValidationConditionAssemblyError
      (CheckedValidationCondition model) := do
  let leftStartDeclaration ← resolveIteratedOperand model rowGroup leftStart
  let leftFinishDeclaration ← resolveIteratedOperand model rowGroup leftFinish
  let rightStartDeclaration ← resolveIteratedOperand model rowGroup rightStart
  let rightFinishDeclaration ← resolveIteratedOperand model rowGroup rightFinish
  fromIteratedDateRange model rowGroup fun scope =>
    elaborateIteratedConstructionPair model scope leftStartDeclaration.id
      leftFinishDeclaration.id rightStartDeclaration.id
      rightFinishDeclaration.id comparison

/-- One constructed range compared with one stored range at the rule's own row. -/
def fromIteratedDateRangeConstructionAgainstStored (model : FlatModel)
    (rowGroup : GroupPath) (start finish stored : SurfaceFieldPath)
    (position : DateRangeConstructionPosition) (comparison : EqualityOp) :
    Except ValidationConditionAssemblyError
      (CheckedValidationCondition model) := do
  let startDeclaration ← resolveIteratedOperand model rowGroup start
  let finishDeclaration ← resolveIteratedOperand model rowGroup finish
  let storedDeclaration ← resolveIteratedFieldValueRead model rowGroup stored
  fromIteratedDateRange model rowGroup fun scope =>
    elaborateIteratedConstructionStoredComparison model scope
      startDeclaration.id finishDeclaration.id storedDeclaration.id position
      comparison

/-- One singular DateRange overlap predicate read at the rule's own row. -/
def fromIteratedDateRangeOverlap (model : FlatModel) (rowGroup : GroupPath)
    (authored : SurfaceFieldEntitySource) (writtenGroup : GroupPath := rowGroup) :
    Except ValidationConditionAssemblyError
      (CheckedValidationCondition model) :=
  fromIteratedDateRange model rowGroup fun scope =>
    elaborateIteratedOverlap model rowGroup scope authored writtenGroup

/-- Resolve one checked RNU source and retain it as an ordinary leaf in the shared condition tree. -/
def fromRepetitionNotUnique (model : FlatModel) (rowGroup : GroupPath)
    (authored : SurfaceRepetitionNotUniqueSource) (writtenGroup : GroupPath) :
    Except ValidationConditionAssemblyError
      (CheckedValidationCondition model) := do
  let source ←
    (elaborateRepetitionNotUniqueSource model rowGroup authored writtenGroup)
      |>.mapError .repetitionNotUnique
  checkCore model rowGroup
    (ValidationCondition.repetitionNotUnique source)
    source.modelWellFormed

/-- Resolve the exact measured nonrepeatable-root `CurrentRepetition` condition. The surface accepts an ordinary group path only; the checked leaf keeps its direct filled guard and equality tag indivisible. -/
def fromGuardedRootCurrentRepetition
    (model : FlatModel) (rowGroup : GroupPath)
    (guard : SurfaceFieldPath) (group : SurfaceGroupPath)
    (comparison : RootCurrentRepetitionComparison) :
    Except ValidationConditionAssemblyError
      (CheckedValidationCondition model) :=
  match hModel : model.validate with
  | .error error => .error (.invalidModel error)
  | .ok () => do
      let declaration ←
        (model.resolveNonrepeatableFieldUnchecked rowGroup guard)
          |>.mapError .fieldReference
      let resolved ← group.resolveAgainst rowGroup
        |>.mapError (.groupReference ∘ .reference)
      if !model.hasGroupPath resolved then
        throw (.groupReference (model.unknownGroupError resolved))
      checkCore model rowGroup
        (ValidationCondition.guardedRootCurrentRepetition
          declaration resolved comparison)
        (by rw [hModel]; rfl)

/-- Resolve the maintained same-group repeatable `CurrentRepetition` condition. The direct filled guard supplies the iteration scope; the group declaration supplies the exact coordinate identity. -/
def fromGuardedRepeatableCurrentRepetition
    (model : FlatModel) (rowGroup : GroupPath)
    (guard : SurfaceFieldPath) (group : SurfaceGroupPath)
    (comparison : RepeatableCurrentRepetitionComparison) :
    Except ValidationConditionAssemblyError
      (CheckedValidationCondition model) :=
  match hModel : model.validate with
  | .error error => .error (.invalidModel error)
  | .ok () => do
      let declaration ←
        (model.resolveFieldDeclarationUnchecked rowGroup guard)
          |>.mapError .fieldReference
      if declaration.repeatableScope.isEmpty then
        throw (.repeatableFieldRequired declaration.path)
      let source ← checkCurrentRepetitionSource model rowGroup group
        |>.mapError
          ValidationConditionAssemblyError.ofCurrentRepetitionSourceError
      checkCore model rowGroup
        (ValidationCondition.guardedRepeatableCurrentRepetition
          declaration source comparison)
        (by rw [hModel]; rfl)

private def resolveGroupListOperand (model : FlatModel) (rowGroup writtenGroup : GroupPath) :
    SurfaceGroupListOperand →
      Except ValidationConditionAssemblyError
        (ResolvedGroupListOperand model)
  | .field reference => do
      let declaration ←
        (model.resolveNonrepeatableFieldUnchecked rowGroup reference writtenGroup).mapError
          .fieldReference
      pure (.field declaration)
  | .group reference => do
      let resolved ←
        model.resolveValidationBoundFixedGroupReference rowGroup reference writtenGroup
        |>.mapError ValidationConditionAssemblyError.groupReference
      pure (.group resolved)
  | .starredGroup reference => do
      let source ←
        (elaborateStarredGroupOperandSource model rowGroup reference)
          |>.mapError fun error => .starredGroup (error.placeBelowStar model rowGroup writtenGroup)
      let (groupPath, bindingScope) := match source with
        | .terminalRepeatable checked => (checked.group.path, checked.path.bindingScope)
        | .terminalPresence checked => (checked.groupPath, checked.path.bindingScope)
      -- A level above the first star is read per row, so the walk answers ahead of every list gate
      -- ([inbound](../../../docs/SOURCES.md#inbound-2026-09-25-operator-gates-wait)).
      if let some unbound := model.refusedReadLevel? rowGroup writtenGroup bindingScope then
        throw (.groupReference (.unboundOperandLevel groupPath unbound))
      match source with
      | .terminalRepeatable checked => pure (.starredGroup checked)
      | .terminalPresence checked => pure (.starredGroupPresence checked)

private def resolveGroupListOperands (model : FlatModel) (rowGroup writtenGroup : GroupPath) :
    List SurfaceGroupListOperand →
      Except ValidationConditionAssemblyError
        (List (ResolvedGroupListOperand model))
  | [] => pure []
  | operand :: rest => do
      let resolved ← resolveGroupListOperand model rowGroup writtenGroup operand
      pure (resolved :: (← resolveGroupListOperands model rowGroup writtenGroup rest))

/-- Fixed singletons have an existing checked scalar owner. Keeping them out of the list leaf prevents a second representation of field or group presence. -/
private def singletonGroupListCondition? (operator : GroupFillQuantifier) :
    ResolvedGroupListOperand model → Option (ValidationCondition model)
  | .field declaration =>
      match operator with
      | .atLeastOneGroupFilled =>
          some (ValidationCondition.flat
            (.fieldFilled declaration.toPresenceField))
      | .noGroupFilled =>
          some (ValidationCondition.flat
            (.fieldNotFilled declaration.toPresenceField))
      | .allGroupsFilled | .notAllGroupsFilled
      | .groupsNotCollectivelyFilled => none
  | .group reference =>
      match operator with
      | .atLeastOneGroupFilled =>
          some (ValidationCondition.groupPresence .filled reference)
      | .noGroupFilled =>
          some (ValidationCondition.groupPresence .notFilled reference)
      | .allGroupsFilled | .notAllGroupsFilled
      | .groupsNotCollectivelyFilled => none
  | .starredGroup _ | .starredGroupPresence _ => none

/-- Resolve one field/group entity list and enforce the kernel's shared duplicate/overlap checks plus its operator-specific arity, root-group, and wildcard gates. The two count-zero/count-positive members retain checked starred-group topology beside plain operands. -/
def fromGroupList (model : FlatModel) (rowGroup : GroupPath)
    (operator : GroupFillQuantifier)
    (operands : List SurfaceGroupListOperand) (writtenGroup : GroupPath := rowGroup) :
    Except ValidationConditionAssemblyError (CheckedValidationCondition model) :=
  match hModel : model.validate with
  | .error error => .error (.invalidModel error)
  | .ok () => do
      let resolved ← resolveGroupListOperands model rowGroup writtenGroup operands
      if resolved.isEmpty then throw .emptyGroupList
      match ResolvedGroupListOperands.firstOverlap? resolved with
      | some (left, right) =>
          throw (ValidationConditionAssemblyError.overlappingGroupListOperands left right)
      | none => pure ()
      match resolved.find? ResolvedGroupListOperand.isRootGroup with
      | some root =>
          if operator.requiresMultipleOperands then
            throw (.rootGroupInGroupList root.entityPath)
          else if resolved.length != 1 then
            throw (.rootGroupRequiresSoleOperand root.entityPath)
      | none => pure ()
      -- The star gate answers behind the root gate: a sole starred root draws the root class under a
      -- quantifier that forbids a star. No row measures a star beside an overlap, so its place after
      -- the overlap gate is the one ordering consistent with every measured row, not a measurement
      -- ([inbound](../../../docs/SOURCES.md#inbound-2026-09-24c-group-operand-walk)).
      if operator.requiresMultipleOperands &&
          resolved.any ResolvedGroupListOperand.isStarred then
        throw (.starredGroupNotAllowed operator)
      match resolved with
      | [operand] =>
          if operand.isStarred then
            checkCore model rowGroup
              (ValidationCondition.groupList operator resolved)
              (by rw [hModel]; rfl)
          else
            match singletonGroupListCondition? operator operand with
            | some condition =>
                checkCore model rowGroup condition (by rw [hModel]; rfl)
            | none => throw .groupListNeedsMultipleOperands
      | _ =>
          checkCore model rowGroup (ValidationCondition.groupList operator resolved)
            (by rw [hModel]; rfl)

private def combine (constructor : ValidationCondition model →
    ValidationCondition model → ValidationCondition model)
    (left right : CheckedValidationCondition model) :
    Except ValidationConditionAssemblyError (CheckedValidationCondition model) :=
  if !left.core.repetitionNotUniqueSources.isEmpty &&
      !right.core.repetitionNotUniqueSources.isEmpty then
    .error .multipleRepetitionNotUnique
  else if left.rowGroup != right.rowGroup then
    .error (.rowGroupMismatch left.rowGroup right.rowGroup)
  else if left.declaringGroup != right.declaringGroup then
    .error (.declaringGroupMismatch left.declaringGroup right.declaringGroup)
  else
    checkCore model left.rowGroup (constructor left.core right.core)
      left.modelWellFormed left.declaringGroup

def and (left right : CheckedValidationCondition model) :
    Except ValidationConditionAssemblyError (CheckedValidationCondition model) :=
  combine .and left right

def or (left right : CheckedValidationCondition model) :
    Except ValidationConditionAssemblyError (CheckedValidationCondition model) :=
  combine .or left right

end CheckedValidationCondition

end A12Kernel
