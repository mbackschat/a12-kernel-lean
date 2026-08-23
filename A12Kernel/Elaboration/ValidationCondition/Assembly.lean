import A12Kernel.Elaboration.ValidationCondition.Iteration

/-! # Checked validation-condition assembly -/

namespace A12Kernel

inductive ValidationConditionAssemblyError where
  | invalidModel (error : ResolveError)
  | groupReference (error : SingleGroupElabError)
  | fieldReference (error : ResolveError)
  | starredGroup (error : StarredGroupElabError)
  | starredGroupNotAllowed (operator : GroupFillQuantifier)
  | repeatableFieldRequired (path : List String)
  | unknownGroup (path : GroupPath)
  | repeatableGroupRequiresAddress (path : GroupPath)
  | emptyGroupList
  | groupListNeedsMultipleOperands
  | rootGroupInGroupList (path : GroupPath)
  | rootGroupRequiresSoleOperand (path : GroupPath)
  | overlappingGroupListOperands (left right : List String)
  | rowGroupMismatch (left right : GroupPath)
  | repetitionNotUnique (error : RepetitionNotUniqueElabError)
  | iteratedDateRange (error : IteratedDateRangeConditionElabError)
  | multipleRepetitionNotUnique
  | incoherentCore
  deriving Repr, DecidableEq

/-- A mixed resolved tree certified against one validated model and one exact rule-instance group. -/
structure CheckedValidationCondition (model : FlatModel) where
  rowGroup : GroupPath
  core : ValidationCondition model
  modelWellFormed : model.validate.isOk = true
  wellFormed : core.wellFormedBool rowGroup = true

private def ValidationConditionAssemblyError.ofFixedGroupReferenceError :
    FixedGroupReferenceError → ValidationConditionAssemblyError
  | .reference error => .groupReference error
  | .unknownGroup path => .unknownGroup path
  | .repeatableGroupRequiresAddress path =>
      .repeatableGroupRequiresAddress path

private def ValidationConditionAssemblyError.ofCurrentRepetitionSourceError :
    CurrentRepetitionSourceElabError → ValidationConditionAssemblyError
  | .model error => .invalidModel error
  | .reference error => .groupReference error
  | .group error => .groupReference (.resolve error)

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
  | .repeatableGroupRequiresAddress _ => some .noWildcard
  | .unknownGroup _ => some .invalidEntity
  | _ => none

end ValidationConditionAssemblyError

namespace CheckedValidationCondition

/-- Public checked-tree query used by Kernel 30.8.1 partial-validation consumers before relevance or execution. -/
def hasHaving (condition : CheckedValidationCondition model) : Bool :=
  condition.core.hasHaving

/-- Certify a resolved mixed core once after a semantic desugaring has assembled its complete tree. -/
def checkCore (model : FlatModel) (rowGroup : GroupPath)
    (core : ValidationCondition model) (modelWellFormed : model.validate.isOk = true) :
    Except ValidationConditionAssemblyError (CheckedValidationCondition model) :=
  if hCore : core.wellFormedBool rowGroup = true then
    .ok { rowGroup, core, modelWellFormed, wellFormed := hCore }
  else
    .error .incoherentCore

/-- Lift a checked flat tree without nesting or changing its connective shape. -/
def fromFlat (condition : CheckedFlatCondition model) :
    Except ValidationConditionAssemblyError (CheckedValidationCondition model) :=
  checkCore model condition.rowGroup (ValidationCondition.flat condition.core)
    condition.modelWellFormed

/-- Lift one checked numeric comparison at its certified rule-instance group. -/
def fromNumeric (comparison : CheckedNumericComparison model) :
    Except ValidationConditionAssemblyError (CheckedValidationCondition model) :=
  checkCore model comparison.rowGroup
    (ValidationCondition.numericIn comparison.operandScope comparison.core)
    comparison.modelWellFormed

/-- Lift one checked ordered-numeric comparison without reconstructing or flattening its authored expression tree. -/
def fromOrderedNumeric
    (comparison : CheckedOrderedNumericComparison model) :
    Except ValidationConditionAssemblyError (CheckedValidationCondition model) :=
  checkCore model comparison.rowGroup
    (ValidationCondition.orderedNumericIn
      comparison.operandScope comparison.core)
    comparison.modelWellFormed

  /-- Resolve and certify one group-presence predicate against the same model and declaring group used by the surrounding rule. Repeatable ancestry is retained for the addressed whole-rule route rather than rejected as a fixed-list operand. -/
def fromGroupPresence (model : FlatModel) (rowGroup : GroupPath)
    (reference : SurfaceGroupReference) (operator : GroupPresenceOperator) :
    Except ValidationConditionAssemblyError (CheckedValidationCondition model) :=
  match hModel : model.validate with
  | .error error => .error (.invalidModel error)
  | .ok () => do
      let resolved ← reference.resolveAgainst rowGroup
        |>.mapError ValidationConditionAssemblyError.groupReference
      if !model.hasGroupPath resolved.path then
        throw (.unknownGroup resolved.path)
      checkCore model rowGroup
        (ValidationCondition.groupPresence operator resolved)
        (by rw [hModel]; rfl)

/-- Resolve one ordinary non-starred repeatable field presence reference. The declaration itself is the checked source; no wildcard topology or caller-supplied environment is manufactured here. -/
def fromRepeatableFieldPresence (model : FlatModel) (rowGroup : GroupPath)
    (operator : RepeatableFieldPresenceOperator)
    (reference : SurfaceFieldPath) :
    Except ValidationConditionAssemblyError
      (CheckedValidationCondition model) :=
  match hModel : model.validate with
  | .error error => .error (.invalidModel error)
  | .ok () => do
      let declaration ←
        (model.resolveFieldDeclarationUnchecked rowGroup reference)
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

/-- One stored-versus-stored DateRange equality read at the rule's own row. -/
def fromIteratedDateRangeEquality (model : FlatModel) (rowGroup : GroupPath)
    (comparison : EqualityOp) (left right : SurfaceFieldPath) :
    Except ValidationConditionAssemblyError
      (CheckedValidationCondition model) := do
  let leftDeclaration ← resolveIteratedOperand model rowGroup left
  let rightDeclaration ← resolveIteratedOperand model rowGroup right
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

/-- One unconfigured yearless DateRange overlap predicate read at the rule's own row. -/
def fromIteratedYearlessDateRangeOverlap (model : FlatModel)
    (rowGroup : GroupPath) (authored : SurfaceFieldEntitySource) :
    Except ValidationConditionAssemblyError
      (CheckedValidationCondition model) :=
  fromIteratedDateRange model rowGroup fun scope =>
    elaborateIteratedYearlessOverlap model rowGroup scope authored

/-- One plural DateRange overlap predicate read at the rule's own row. -/
def fromIteratedDateRangePluralOverlap (model : FlatModel)
    (rowGroup : GroupPath)
    (authored : SurfaceAtLeastOneDateRangeOverlapsSource) :
    Except ValidationConditionAssemblyError
      (CheckedValidationCondition model) :=
  fromIteratedDateRange model rowGroup fun scope =>
    elaborateIteratedPluralOverlap model rowGroup scope authored

/-- One constructed range compared with one stored range at the rule's own row. -/
def fromIteratedDateRangeConstructionAgainstStored (model : FlatModel)
    (rowGroup : GroupPath) (start finish stored : SurfaceFieldPath)
    (position : DateRangeConstructionPosition) (comparison : EqualityOp) :
    Except ValidationConditionAssemblyError
      (CheckedValidationCondition model) := do
  let startDeclaration ← resolveIteratedOperand model rowGroup start
  let finishDeclaration ← resolveIteratedOperand model rowGroup finish
  let storedDeclaration ← resolveIteratedOperand model rowGroup stored
  fromIteratedDateRange model rowGroup fun scope =>
    elaborateIteratedConstructionStoredComparison model scope
      startDeclaration.id finishDeclaration.id storedDeclaration.id position
      comparison

/-- One singular DateRange overlap predicate read at the rule's own row. -/
def fromIteratedDateRangeOverlap (model : FlatModel) (rowGroup : GroupPath)
    (authored : SurfaceFieldEntitySource) :
    Except ValidationConditionAssemblyError
      (CheckedValidationCondition model) :=
  fromIteratedDateRange model rowGroup fun scope =>
    elaborateIteratedOverlap model rowGroup scope authored

/-- Resolve one checked RNU source and retain it as an ordinary leaf in the shared condition tree. -/
def fromRepetitionNotUnique (model : FlatModel) (rowGroup : GroupPath)
    (authored : SurfaceRepetitionNotUniqueSource) :
    Except ValidationConditionAssemblyError
      (CheckedValidationCondition model) := do
  let source ←
    (elaborateRepetitionNotUniqueSource model rowGroup authored)
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
        |>.mapError .groupReference
      if !model.hasGroupPath resolved then
        throw (.unknownGroup resolved)
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

private def resolveGroupListOperand (model : FlatModel) (rowGroup : GroupPath) :
    SurfaceGroupListOperand →
      Except ValidationConditionAssemblyError
        (ResolvedGroupListOperand model)
  | .field reference => do
      let declaration ←
        (model.resolveNonrepeatableFieldUnchecked rowGroup reference).mapError .fieldReference
      pure (.field declaration)
  | .group reference => do
      let resolved ← model.resolveFixedGroupReference rowGroup reference
        |>.mapError ValidationConditionAssemblyError.ofFixedGroupReferenceError
      pure (.group resolved)
  | .starredGroup reference => do
      let source ←
        (elaborateStarredGroupOperandSource model rowGroup reference)
          |>.mapError .starredGroup
      match source with
      | .terminalRepeatable checked => pure (.starredGroup checked)
      | .terminalPresence checked => pure (.starredGroupPresence checked)

private def resolveGroupListOperands (model : FlatModel) (rowGroup : GroupPath) :
    List SurfaceGroupListOperand →
      Except ValidationConditionAssemblyError
        (List (ResolvedGroupListOperand model))
  | [] => pure []
  | operand :: rest => do
      let resolved ← resolveGroupListOperand model rowGroup operand
      pure (resolved :: (← resolveGroupListOperands model rowGroup rest))

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
    (operands : List SurfaceGroupListOperand) :
    Except ValidationConditionAssemblyError (CheckedValidationCondition model) :=
  match hModel : model.validate with
  | .error error => .error (.invalidModel error)
  | .ok () => do
      let resolved ← resolveGroupListOperands model rowGroup operands
      if resolved.isEmpty then throw .emptyGroupList
      if operator.requiresMultipleOperands &&
          resolved.any ResolvedGroupListOperand.isStarred then
        throw (.starredGroupNotAllowed operator)
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
  else if left.rowGroup == right.rowGroup then
    checkCore model left.rowGroup (constructor left.core right.core)
      left.modelWellFormed
  else
    .error (.rowGroupMismatch left.rowGroup right.rowGroup)

def and (left right : CheckedValidationCondition model) :
    Except ValidationConditionAssemblyError (CheckedValidationCondition model) :=
  combine .and left right

def or (left right : CheckedValidationCondition model) :
    Except ValidationConditionAssemblyError (CheckedValidationCondition model) :=
  combine .or left right

end CheckedValidationCondition

end A12Kernel
