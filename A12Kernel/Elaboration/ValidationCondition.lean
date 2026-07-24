import A12Kernel.Elaboration.NumericValidation
import A12Kernel.Elaboration.SingleGroup
import A12Kernel.Elaboration.ValidationContext

/-! # Shared resolved validation conditions

This boundary joins the established flat leaves and resolved numeric-expression comparisons under one connective tree. It deliberately begins after each leaf family's checked elaboration; a later checked whole-rule capsule must preserve those certificates rather than accepting forged cores.
-/

namespace A12Kernel

/-- One authored operand of the kernel's fixed group-list condition family. Despite the language-level name, the checked entity list admits both fields and groups. Starred group scopes remain a separate SG2 source shape. -/
inductive SurfaceGroupListOperand where
  | field (reference : SurfaceFieldPath)
  | group (reference : SurfaceGroupReference)
  deriving Repr, DecidableEq

/-- A fixed group-list operand after model-owned field/group resolution. A field retains its exact declaration so overlap and checked-core coherence cannot be forged from an ID alone. -/
inductive ResolvedGroupListOperand where
  | field (declaration : FlatFieldDecl)
  | group (reference : ResolvedGroupReference)
  deriving Repr, DecidableEq

/-- Presence operators for an ordinary non-starred repeatable field reference. Evaluation reuses the established scalar presence observation after the rule environment has selected one exact field instance. -/
inductive RepeatableFieldPresenceOperator where
  | filled
  | notFilled
  deriving Repr, DecidableEq

namespace RepeatableFieldPresenceOperator

def canFireOnEmpty : RepeatableFieldPresenceOperator → Bool
  | .filled => false
  | .notFilled => true

def eval (operator : RepeatableFieldPresenceOperator)
    (observation : CellObservation) : Verdict :=
  match operator with
  | .filled => observation.evalValidationFilled
  | .notFilled => observation.evalValidationNotFilled

end RepeatableFieldPresenceOperator

namespace ResolvedGroupListOperand

def entityPath : ResolvedGroupListOperand → List String
  | .field declaration => declaration.path
  | .group reference => reference.path

def isRootGroup : ResolvedGroupListOperand → Bool
  | .field _ => false
  | .group reference => reference.isRoot

def referencesField (operand : ResolvedGroupListOperand)
    (model : FlatModel) (field : FieldId) : Bool :=
  match operand with
  | .field declaration => declaration.id == field
  | .group reference => reference.referencesField model field

def wellFormedBool (operand : ResolvedGroupListOperand)
    (model : FlatModel) (rowGroup : GroupPath) : Bool :=
  match operand with
  | .field declaration =>
      match model.lookupUniqueId declaration.id with
      | .ok checked =>
          checked == declaration && declaration.repeatableScope.isEmpty
      | .error _ => false
  | .group reference =>
      reference.fixedWellFormedBool model rowGroup

/-- Kernel entity-list duplicate checking rejects direct duplicates and every group/descendant pair. Sibling fields and sibling groups remain independent. -/
def overlaps (left right : ResolvedGroupListOperand) : Bool :=
  match left, right with
  | .field leftDeclaration, .field rightDeclaration =>
      leftDeclaration.id == rightDeclaration.id
  | .group leftReference, .group rightReference =>
      leftReference.overlaps rightReference
  | .group reference, .field declaration
  | .field declaration, .group reference =>
      reference.path.isPrefixOf declaration.groupPath

end ResolvedGroupListOperand

namespace ResolvedGroupListOperands

def firstOverlap? : List ResolvedGroupListOperand →
    Option (List String × List String)
  | [] => none
  | first :: rest =>
      match rest.find? (first.overlaps ·) with
      | some overlapping => some (first.entityPath, overlapping.entityPath)
      | none => firstOverlap? rest

def wellFormedBool (operands : List ResolvedGroupListOperand)
    (model : FlatModel) (rowGroup : GroupPath) : Bool :=
  !operands.isEmpty &&
    1 < operands.length &&
    operands.all (·.wellFormedBool model rowGroup) &&
    (firstOverlap? operands).isNone &&
    !operands.any ResolvedGroupListOperand.isRootGroup

end ResolvedGroupListOperands

/-- The currently resolved validation leaf families, indexed by the one checked model that owns every retained source certificate. -/
inductive ValidationConditionLeaf (model : FlatModel) where
  | flat (condition : FlatConditionLeaf)
  | numeric (scope : NumericOperandScope) (comparison : NumericComparison)
  | orderedNumeric (scope : NumericOperandScope)
      (comparison : OrderedNumericComparison model)
  | groupPresence (operator : GroupPresenceOperator)
      (reference : ResolvedGroupReference)
  | groupList (operator : GroupFillQuantifier)
      (operands : List ResolvedGroupListOperand)
  | repeatableFieldPresence (operator : RepeatableFieldPresenceOperator)
      (declaration : FlatFieldDecl)

/-- One connective tree whose leaves may be ordinary flat clauses or model-certified resolved numeric-expression comparisons. -/
abbrev ValidationCondition (model : FlatModel) :=
  ConditionTree (ValidationConditionLeaf model)

namespace ValidationCondition

/-- Embed an established flat tree without retaining a nested connective tree. -/
def flat (condition : FlatCondition) : ValidationCondition model :=
  condition.map .flat

/-- Admit one resolved numeric comparison as a leaf. Checked construction remains with `CheckedNumericComparison`. -/
def numeric (comparison : NumericComparison) : ValidationCondition model :=
  .leaf (.numeric .sameGroup comparison)

/-- Preserve the checked operand policy when embedding a numeric comparison. -/
def numericIn (scope : NumericOperandScope)
    (comparison : NumericComparison) : ValidationCondition model :=
  .leaf (.numeric scope comparison)

/-- Embed a numeric comparison whose checked atoms own relevance timing. -/
def orderedNumericIn (scope : NumericOperandScope)
    (comparison : OrderedNumericComparison model) : ValidationCondition model :=
  .leaf (.orderedNumeric scope comparison)

/-- Embed one resolved scalar group-presence predicate without re-traversing document state. -/
def groupPresence (operator : GroupPresenceOperator)
    (reference : ResolvedGroupReference) : ValidationCondition model :=
  .leaf (.groupPresence operator reference)

/-- Embed one fixed checked field/group presence list without expanding it into a parallel connective tree. -/
def groupList (operator : GroupFillQuantifier)
    (operands : List ResolvedGroupListOperand) : ValidationCondition model :=
  .leaf (.groupList operator operands)

/-- Embed one ordinary non-starred repeatable field presence reference. Checked construction retains the exact model declaration; whole-rule assembly derives iteration from this leaf rather than accepting caller-supplied scope metadata. -/
def repeatableFieldPresence (operator : RepeatableFieldPresenceOperator)
    (declaration : FlatFieldDecl) : ValidationCondition model :=
  .leaf (.repeatableFieldPresence operator declaration)

end ValidationCondition

namespace ResolvedGroupReference

/-- A scalar group-presence leaf either names a nonrepeatable ordinary group, or uses `RuleGroup` to bind the already-selected concrete rule instance. Wider repeatable addressing must be resolved before this boundary grows. -/
def scalarPresenceWellFormedBool (reference : ResolvedGroupReference)
    (model : FlatModel) (rowGroup : GroupPath) : Bool :=
  reference.fixedWellFormedBool model rowGroup

end ResolvedGroupReference

def ResolvedGroupListOperand.evalPresence
    (context : ValidationEvaluationContext) (isRelevant : FlatRelevance) :
    ResolvedGroupListOperand → GroupListPresenceState
  | .field declaration =>
      if isRelevant declaration.id then
        (declaration.toPresenceField.observeValidation context.fields).asGroupListPresence
      else
        .unavailable
  | .group reference =>
      match context.groups reference.path with
      | some state => state.asGroupListPresence
      | none => .unavailable

namespace ValidationConditionLeaf

def canFireOnEmpty : ValidationConditionLeaf model → Bool
  | .flat condition => condition.canFireOnEmpty
  | .numeric _ _ | .orderedNumeric _ _ => false
  | .groupPresence operator _ => operator.canFireOnEmpty
  | .groupList operator _ => operator.canFireOnEmpty
  | .repeatableFieldPresence operator _ => operator.canFireOnEmpty

def referencesField : ValidationConditionLeaf model → FieldId → Bool
  | .flat condition, field => condition.referencesField field
  | .numeric _ comparison, field => comparison.referencesField model field
  | .orderedNumeric _ comparison, field =>
      comparison.referencesField field
  | .groupPresence _ reference, field => reference.referencesField model field
  | .groupList _ operands, field =>
      operands.any fun operand => operand.referencesField model field
  | .repeatableFieldPresence _ declaration, field =>
      declaration.id == field

/-- Whether a leaf retains any `Having` filter in its checked source. Only the model-indexed ordered numeric carrier can currently own such a source; scalar leaves cannot manufacture the marker. -/
def hasHaving : ValidationConditionLeaf model → Bool
  | .orderedNumeric _ comparison => comparison.hasHaving
  | .flat _ | .numeric _ _ | .groupPresence _ _ | .groupList _ _
  | .repeatableFieldPresence _ _ => false

/-- Whether this leaf retains a repeatable numeric source and therefore cannot use the scalar checked evaluator. -/
def requiresAddressedValidation : ValidationConditionLeaf model → Bool
  | .orderedNumeric _ comparison =>
      comparison.requiresAddressedValidation
  | .repeatableFieldPresence _ _ => true
  | _ => false

/-- Static admission reuses each leaf family's existing checked core predicate. -/
def wellFormedBool (rowGroup : GroupPath) :
    ValidationConditionLeaf model → Bool
  | .flat condition => condition.wellFormedBool model
  | .numeric scope comparison =>
      comparison.wellFormedInBool model rowGroup scope
  | .orderedNumeric scope comparison =>
      comparison.wellFormedInBool rowGroup scope
  | .groupPresence _ reference =>
      reference.scalarPresenceWellFormedBool model rowGroup
  | .groupList _ operands =>
      ResolvedGroupListOperands.wellFormedBool operands model rowGroup
  | .repeatableFieldPresence _ declaration =>
      match model.lookupUniqueId declaration.id with
      | .ok checked =>
          checked == declaration && !declaration.repeatableScope.isEmpty
      | .error _ => false

/-- Evaluate one reached leaf with its own relevance rule. Ordinary numeric expressions require every field atom, ordered numeric atoms gate their own reached sources, and flat leaf rules retain their existing operator-specific checks. -/
def evalSelected (context : ValidationEvaluationContext)
    (isRelevant : FlatRelevance) :
    ValidationConditionLeaf model → Verdict
  | .flat condition => condition.evalSelected context.fields isRelevant
  | .numeric _ comparison =>
      if comparison.allRelevant isRelevant then
        comparison.evalSelectedWithGroups context
      else .unknown
  | .orderedNumeric _ comparison =>
      comparison.evalSelected context isRelevant
  | .groupPresence operator reference =>
      match context.groups reference.path with
      | some state => operator.eval state
      | none => .unknown
  | .groupList operator operands =>
      (operator.evalPresence
        (operands.map fun operand => operand.evalPresence context isRelevant)).asConservativeVerdict
  | .repeatableFieldPresence _ _ => .unknown

/-- Evaluate one addressed leaf through the same relevance rules. Only the model-indexed ordered numeric branch can produce a structural addressing error; every existing scalar/group leaf remains the exact pure evaluator lifted into that channel. -/
def evalAddressed (context : AddressedValidationEvaluationContext model) :
    ValidationConditionLeaf model → Except StarAddressingError Verdict
  | .orderedNumeric _ comparison => comparison.evalAddressed context
  | .repeatableFieldPresence operator declaration =>
      pure (operator.eval
        (observeCell .validation (context.read context.outer declaration.id)))
  | leaf => pure (leaf.evalSelected context.scalar context.directRelevant)

end ValidationConditionLeaf

namespace ValidationCondition

def canFireOnEmpty (condition : ValidationCondition model) : Bool :=
  condition.evalBool ValidationConditionLeaf.canFireOnEmpty

def referencesField (condition : ValidationCondition model)
    (field : FieldId) : Bool :=
  condition.anyLeaf fun leaf => leaf.referencesField field

private def repeatableScopePrefix : List RepeatableLevel →
    List RepeatableLevel → Bool
  | [], _ => true
  | _, [] => false
  | left :: leftRest, right :: rightRest =>
      left == right && repeatableScopePrefix leftRest rightRest

inductive RuleIterationScopeError where
  | incompatibleScopes (left right : List RepeatableLevel)
  deriving Repr, DecidableEq

private def mergeIterationScopes
    (left right : Option (List RepeatableLevel)) :
    Except RuleIterationScopeError (Option (List RepeatableLevel)) :=
  match left, right with
  | none, scope | scope, none => pure scope
  | some leftScope, some rightScope =>
      if repeatableScopePrefix leftScope rightScope then
        pure (some rightScope)
      else if repeatableScopePrefix rightScope leftScope then
        pure (some leftScope)
      else
        throw (.incompatibleScopes leftScope rightScope)

/-- Derive one ordinary nonparallel rule-iteration scope from non-starred repeatable references. Nested compatible references select the deeper scope; sibling/cross-branch scopes remain explicit unsupported parallel work. Aggregate stars do not enter this traversal. -/
def ordinaryIterationScope :
    ValidationCondition model →
      Except RuleIterationScopeError (Option (List RepeatableLevel))
  | .leaf (.repeatableFieldPresence _ declaration) =>
      pure (some declaration.repeatableScope)
  | .leaf _ => pure none
  | .and left right | .or left right => do
      mergeIterationScopes
        (← ordinaryIterationScope left) (← ordinaryIterationScope right)

/-- Ordinary repeatable field declarations in authored tree order. Whole-rule checked-document execution resolves these exact cells before evaluation so a structural address failure cannot be collapsed into semantic UNKNOWN. -/
def ordinaryRepeatableFields (condition : ValidationCondition model) :
    List FlatFieldDecl :=
  match condition with
  | .leaf (.repeatableFieldPresence _ declaration) => [declaration]
  | .leaf _ => []
  | .and left right | .or left right =>
      ordinaryRepeatableFields left ++ ordinaryRepeatableFields right

/-- The first whole-rule route accepts established nonrepeatable flat leaves plus ordinary repeatable presence leaves. Specialized addressed sources retain their existing owners until their rule-environment bridge closes. -/
def supportsOrdinaryIteration
    (condition : ValidationCondition model) : Bool :=
  condition.allLeaves fun
    | .flat _ | .repeatableFieldPresence _ _ => true
    | _ => false

/-- Discover a filtered source across the complete checked connective tree. Unlike verdict evaluation, this static traversal never short-circuits on a decisive branch. -/
def hasHaving (condition : ValidationCondition model) : Bool :=
  condition.anyLeaf ValidationConditionLeaf.hasHaving

/-- Public execution-mode query for checked consumers. A true result requires the full addressed evaluator; choosing the scalar route is an explicit context error rather than semantic UNKNOWN. -/
def requiresAddressedValidation
    (condition : ValidationCondition model) : Bool :=
  condition.anyLeaf ValidationConditionLeaf.requiresAddressedValidation

def wellFormedBool (condition : ValidationCondition model)
    (rowGroup : GroupPath) : Bool :=
  condition.allLeaves fun leaf => leaf.wellFormedBool rowGroup

/-- Evaluate a row-selected mixed tree through the sole connective evaluator. -/
def evalSelected (condition : ValidationCondition model)
    (context : ValidationEvaluationContext)
    (isRelevant : FlatRelevance := fun _ => true) : Verdict :=
  condition.evalVerdict fun leaf => leaf.evalSelected context isRelevant

/-- Apply the ordinary full-validation content gate to a mixed resolved tree. -/
def evalFull (condition : ValidationCondition model)
    (context : ValidationEvaluationContext)
    (hasContent : Bool) : Verdict :=
  if hasContent || condition.canFireOnEmpty then condition.evalSelected context
  else .notFired

/-- Evaluate one row-selected checked tree while retaining structural addressing failure outside the verdict algebra. The generic effectful connective fold preserves the ordinary decisive-left short-circuit boundary. -/
def evalAddressed (condition : ValidationCondition model)
    (context : AddressedValidationEvaluationContext model) :
    Except StarAddressingError Verdict :=
  condition.evalVerdictExcept fun leaf => leaf.evalAddressed context

/-- Apply the ordinary full-validation content gate to the addressed tree without sampling any repeatable source on an ineligible empty row. -/
def evalAddressedFull (condition : ValidationCondition model)
    (context : AddressedValidationEvaluationContext model)
    (hasContent : Bool) : Except StarAddressingError Verdict :=
  if hasContent || condition.canFireOnEmpty then condition.evalAddressed context
  else pure .notFired

end ValidationCondition

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

/-- Resolve and certify one scalar group-presence predicate against the same model and declaring group used by the surrounding rule. -/
def fromGroupPresence (model : FlatModel) (rowGroup : GroupPath)
    (reference : SurfaceGroupReference) (operator : GroupPresenceOperator) :
    Except ValidationConditionAssemblyError (CheckedValidationCondition model) :=
  match hModel : model.validate with
  | .error error => .error (.invalidModel error)
  | .ok () => do
      let resolved ← model.resolveFixedGroupReference rowGroup reference
        |>.mapError ValidationConditionAssemblyError.ofFixedGroupReferenceError
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
  if left.rowGroup == right.rowGroup then
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
