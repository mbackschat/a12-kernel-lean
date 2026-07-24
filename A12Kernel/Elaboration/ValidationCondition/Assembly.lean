import A12Kernel.Elaboration.ValidationCondition.Iteration

/-! # Checked validation-condition assembly -/

namespace A12Kernel

inductive ValidationConditionAssemblyError where
  | invalidModel (error : ResolveError)
  | groupReference (error : SingleGroupElabError)
  | fieldReference (error : ResolveError)
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

private def resolveGroupListOperand (model : FlatModel) (rowGroup : GroupPath) :
    SurfaceGroupListOperand →
      Except ValidationConditionAssemblyError ResolvedGroupListOperand
  | .field reference => do
      let declaration ←
        (model.resolveNonrepeatableFieldUnchecked rowGroup reference).mapError .fieldReference
      pure (.field declaration)
  | .group reference => do
      let resolved ← model.resolveFixedGroupReference rowGroup reference
        |>.mapError ValidationConditionAssemblyError.ofFixedGroupReferenceError
      pure (.group resolved)

private def resolveGroupListOperands (model : FlatModel) (rowGroup : GroupPath) :
    List SurfaceGroupListOperand →
      Except ValidationConditionAssemblyError (List ResolvedGroupListOperand)
  | [] => pure []
  | operand :: rest => do
      let resolved ← resolveGroupListOperand model rowGroup operand
      pure (resolved :: (← resolveGroupListOperands model rowGroup rest))

/-- Fixed singletons have an existing checked scalar owner. Keeping them out of the list leaf prevents a second representation of field or group presence. -/
private def singletonGroupListCondition? (operator : GroupFillQuantifier) :
    ResolvedGroupListOperand → Option (ValidationCondition model)
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

/-- Resolve one fixed nonrepeatable field/group list and enforce the kernel's shared duplicate/overlap checks plus its operator-specific arity and root-group gates. Starred group operands remain with the checked SG2 topology owner. -/
def fromGroupList (model : FlatModel) (rowGroup : GroupPath)
    (operator : GroupFillQuantifier)
    (operands : List SurfaceGroupListOperand) :
    Except ValidationConditionAssemblyError (CheckedValidationCondition model) :=
  match hModel : model.validate with
  | .error error => .error (.invalidModel error)
  | .ok () => do
      let resolved ← resolveGroupListOperands model rowGroup operands
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
      match resolved with
      | [operand] =>
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
