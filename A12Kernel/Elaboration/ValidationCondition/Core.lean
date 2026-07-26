import A12Kernel.Elaboration.NumericValidation
import A12Kernel.Elaboration.CheckedGroupPresence
import A12Kernel.Elaboration.RepetitionNotUnique
import A12Kernel.Elaboration.SingleGroup
import A12Kernel.Elaboration.StarGroup
import A12Kernel.Elaboration.ValidationContext

/-! # Shared resolved validation conditions

This boundary joins the established flat leaves and resolved numeric-expression comparisons under one connective tree. It deliberately begins after each leaf family's checked elaboration; a later checked whole-rule capsule must preserve those certificates rather than accepting forged cores.
-/

/-! This focused module owns resolved validation-condition leaves, connective evaluation, and dependency discovery. Static iteration scope lives in `StaticIteration`. -/

namespace A12Kernel

/-- One authored operand of the kernel's group-list condition family. Despite the language-level name, the checked entity list admits fields, ordinary groups, and — for two operators — groups below starred repeatable ancestry. -/
inductive SurfaceGroupListOperand where
  | field (reference : SurfaceFieldPath)
  | group (reference : SurfaceGroupReference)
  | starredGroup (reference : SurfaceStarGroupPath)
  deriving Repr, DecidableEq

/-- A group-list operand after model-owned resolution. Every variant retains its exact declaration or checked source, so overlap, topology, and checked-core coherence cannot be forged from paths alone. -/
inductive ResolvedGroupListOperand (model : FlatModel) where
  | field (declaration : FlatFieldDecl)
  | group (reference : ResolvedGroupReference)
  | starredGroup (source : CheckedStarredGroupSource model)
  | starredGroupPresence (source : CheckedStarredGroupPresenceSource model)

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

def entityPath : ResolvedGroupListOperand model → List String
  | .field declaration => declaration.path
  | .group reference => reference.path
  | .starredGroup source => source.group.path
  | .starredGroupPresence source => source.groupPath

def isRootGroup : ResolvedGroupListOperand model → Bool
  | .field _ => false
  | .group reference => reference.isRoot
  | .starredGroup source => source.group.path.length == 1
  | .starredGroupPresence source => source.groupPath.length == 1

def isStarred : ResolvedGroupListOperand model → Bool
  | .starredGroup _ | .starredGroupPresence _ => true
  | .field _ | .group _ => false

def referencesField (operand : ResolvedGroupListOperand model)
    (field : FieldId) : Bool :=
  match operand with
  | .field declaration => declaration.id == field
  | .group reference => reference.referencesField model field
  | .starredGroup source =>
      match model.lookupUniqueId field with
      | .ok declaration => source.group.path.isPrefixOf declaration.groupPath
      | .error _ => false
  | .starredGroupPresence source =>
      match model.lookupUniqueId field with
      | .ok declaration => source.groupPath.isPrefixOf declaration.groupPath
      | .error _ => false

def wellFormedBool (operand : ResolvedGroupListOperand model)
    (rowGroup : GroupPath) : Bool :=
  match operand with
  | .field declaration =>
      match model.lookupUniqueId declaration.id with
      | .ok checked =>
          checked == declaration && declaration.repeatableScope.isEmpty
      | .error _ => false
  | .group reference =>
      reference.fixedWellFormedBool model rowGroup
  | .starredGroup source => source.wellFormedBool rowGroup
  | .starredGroupPresence source => source.wellFormedBool rowGroup

private def overlapsStarred (path : GroupPath) :
    ResolvedGroupListOperand model → Bool
  | .field declaration => path.isPrefixOf declaration.groupPath
  | .group reference =>
      reference.path.isPrefixOf path || path.isPrefixOf reference.path
  | .starredGroup source =>
      path != source.group.path &&
        (path.isPrefixOf source.group.path ||
          source.group.path.isPrefixOf path)
  | .starredGroupPresence source =>
      path != source.groupPath &&
        (path.isPrefixOf source.groupPath ||
          source.groupPath.isPrefixOf path)

/-- Kernel entity-list duplicate checking rejects direct non-wildcard duplicates and every strict group/descendant pair. Repeated starred operands and unrelated siblings remain independent authored occurrences. -/
def overlaps (left right : ResolvedGroupListOperand model) : Bool :=
  match left with
  | .field leftDeclaration =>
      match right with
      | .field rightDeclaration =>
          leftDeclaration.id == rightDeclaration.id
      | .group reference =>
          reference.path.isPrefixOf leftDeclaration.groupPath
      | .starredGroup source =>
          source.group.path.isPrefixOf leftDeclaration.groupPath
      | .starredGroupPresence source =>
          source.groupPath.isPrefixOf leftDeclaration.groupPath
  | .group leftReference =>
      match right with
      | .field declaration =>
          leftReference.path.isPrefixOf declaration.groupPath
      | .group rightReference => leftReference.overlaps rightReference
      | .starredGroup source =>
          overlapsStarred (model := model) source.group.path
            (.group leftReference)
      | .starredGroupPresence source =>
          overlapsStarred (model := model) source.groupPath
            (.group leftReference)
  | .starredGroup source => overlapsStarred source.group.path right
  | .starredGroupPresence source => overlapsStarred source.groupPath right

/-- The captured repeatable prefix of a starred group operand; direct operands contribute no ordinary rule-iteration scope. -/
def iterationScope :
    ResolvedGroupListOperand model → Option (List RepeatableLevel)
  | .starredGroup source =>
      let scope :=
        (source.path.axes.take source.path.firstStar).map (·.level)
      if scope.isEmpty then none else some scope
  | .starredGroupPresence source =>
      let scope :=
        (source.path.axes.take source.path.firstStar).map (·.level)
      if scope.isEmpty then none else some scope
  | .field _ | .group _ => none

end ResolvedGroupListOperand

namespace ResolvedGroupListOperands

def firstOverlap? : List (ResolvedGroupListOperand model) →
    Option (List String × List String)
  | [] => none
  | first :: rest =>
      match rest.find? (first.overlaps ·) with
      | some overlapping => some (first.entityPath, overlapping.entityPath)
      | none => firstOverlap? rest

def wellFormedBool (operator : GroupFillQuantifier)
    (operands : List (ResolvedGroupListOperand model))
    (rowGroup : GroupPath) : Bool :=
  !operands.isEmpty &&
    (if operator.requiresMultipleOperands then
      1 < operands.length &&
        !operands.any ResolvedGroupListOperand.isStarred
    else
      operands.length != 1 ||
        operands.any ResolvedGroupListOperand.isStarred) &&
    operands.all (·.wellFormedBool rowGroup) &&
    (firstOverlap? operands).isNone &&
    (!operands.any ResolvedGroupListOperand.isRootGroup ||
      (!operator.requiresMultipleOperands && operands.length == 1))

end ResolvedGroupListOperands

/-- Static contribution of one checked condition subtree at one repeatable level. `unclassified` means the subtree references that level but its operator-specific guard rule has not yet been established. -/
inductive IterationGuardStatus where
  | noReference
  | unguarded
  | guarded
  | unclassified
  deriving Repr, DecidableEq

namespace IterationGuardStatus

/-- An `And` is guarded when either referenced conjunct supplies a known guard. An unclassified referenced conjunct matters only when no sibling already guards the level. -/
def and : IterationGuardStatus → IterationGuardStatus → IterationGuardStatus
  | .guarded, _ | _, .guarded => .guarded
  | .unclassified, _ | _, .unclassified => .unclassified
  | .unguarded, _ | _, .unguarded => .unguarded
  | .noReference, .noReference => .noReference

/-- Every `Or` branch must reference and guard the level. A missing or known-unguarded branch decides failure; an unclassified branch remains explicit only when every other branch is guarded. -/
def or : IterationGuardStatus → IterationGuardStatus → IterationGuardStatus
  | .guarded, .guarded => .guarded
  | .unclassified, .guarded
  | .guarded, .unclassified
  | .unclassified, .unclassified => .unclassified
  | .noReference, .noReference => .noReference
  | _, _ => .unguarded

end IterationGuardStatus

namespace ConditionTree

/-- Fold per-leaf static iteration guards through the kernel's level-local `And`/`Or` admission algebra. -/
def iterationGuardStatus (classify : Leaf → IterationGuardStatus) :
    ConditionTree Leaf → IterationGuardStatus
  | .leaf value => classify value
  | .and left right =>
      IterationGuardStatus.and
        (left.iterationGuardStatus classify)
        (right.iterationGuardStatus classify)
  | .or left right =>
      IterationGuardStatus.or
        (left.iterationGuardStatus classify)
        (right.iterationGuardStatus classify)

end ConditionTree

/-- The currently resolved validation leaf families, indexed by the one checked model that owns every retained source certificate. -/
inductive ValidationConditionLeaf (model : FlatModel) where
  | flat (condition : FlatConditionLeaf)
  | numeric (scope : NumericOperandScope) (comparison : NumericComparison)
  | orderedNumeric (scope : NumericOperandScope)
      (comparison : OrderedNumericComparison model)
  | groupPresence (operator : GroupPresenceOperator)
      (reference : ResolvedGroupReference)
  | groupList (operator : GroupFillQuantifier)
      (operands : List (ResolvedGroupListOperand model))
  | repeatableFieldPresence (operator : RepeatableFieldPresenceOperator)
      (declaration : FlatFieldDecl)
  | repetitionNotUnique
      (source : CheckedRepetitionNotUniqueSource model)

/-- One checked connective tree whose leaves retain their family-specific resolved certificates and evaluation policies. -/
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

/-- Embed one checked field/group entity list without expanding it into a parallel connective tree. Starred topology remains explicit in its model-indexed operand. -/
def groupList (operator : GroupFillQuantifier)
    (operands : List (ResolvedGroupListOperand model)) :
    ValidationCondition model :=
  .leaf (.groupList operator operands)

/-- Embed one ordinary non-starred repeatable field presence reference. Checked construction retains the exact model declaration; whole-rule assembly derives iteration from this leaf rather than accepting caller-supplied scope metadata. -/
def repeatableFieldPresence (operator : RepeatableFieldPresenceOperator)
    (declaration : FlatFieldDecl) : ValidationCondition model :=
  .leaf (.repeatableFieldPresence operator declaration)

/-- Embed one checked branch-independent RNU source as an ordinary condition leaf. Whole-rule execution owns the once-per-scope result preparation. -/
def repetitionNotUnique
    (source : CheckedRepetitionNotUniqueSource model) :
    ValidationCondition model :=
  .leaf (.repetitionNotUnique source)

end ValidationCondition

namespace ResolvedGroupReference

/-- A group-presence leaf retains one known ordinary group path or the exact declaring `RuleGroup`. Whether it needs a row environment is derived separately from the resolved path's repeatable scope. -/
def presenceWellFormedBool (reference : ResolvedGroupReference)
    (model : FlatModel) (rowGroup : GroupPath) : Bool :=
  model.hasGroupPath reference.path &&
    match reference.origin with
    | .path => true
    | .ruleGroup => reference.path == rowGroup

end ResolvedGroupReference

def ResolvedGroupListOperand.evalDirectPresence?
    (context : ValidationEvaluationContext) (isRelevant : FlatRelevance) :
    ResolvedGroupListOperand model → Option GroupListPresenceState
  | .field declaration =>
      some (if isRelevant declaration.id then
        (declaration.toPresenceField.observeValidation
          context.fields).asGroupListPresence
      else
        .unavailable)
  | .group reference =>
      some (match context.groups reference.path with
        | some state => state.asGroupListPresence
        | none => .unavailable)
  | .starredGroup _ | .starredGroupPresence _ => none

def ResolvedGroupListOperand.evalAddressedTally
    (context : AddressedValidationEvaluationContext model) :
    ResolvedGroupListOperand model →
      Except CheckedAddressingError GroupListPresenceTally
  | .field declaration =>
      pure (GroupListPresenceTally.ofStates [if context.directRelevant
          declaration.id then
        (declaration.toPresenceField.observeValidation
          context.scalar.fields).asGroupListPresence
      else
        .unavailable])
  | .group reference =>
      pure (GroupListPresenceTally.ofStates [match context.scalar.groups
          reference.path with
        | some state => state.asGroupListPresence
        | none => .unavailable])
  | .starredGroup source => do
      let document := match context.input with
        | .legacy document _ => document
        | .checked checked => checked.source.toDocument
      let count ← (source.rowCount document context.outer).mapError .addressing
      pure (GroupListPresenceTally.filledOnly count)
  | .starredGroupPresence source =>
      match context.input with
      | .legacy _ _ => .error (.checkedDocumentRequired source.groupPath)
      | .checked document => do
          let topology ←
            (source.resolvedTopology document.source.toDocument context.outer)
              |>.mapError .addressing
          let states ← topology.environments.mapM fun environment => do
            let input ←
              (document.groupPresenceInput source.groupPath environment
                .fullyRelevant false).mapError .group
            pure input.derive.asGroupListPresence
          pure (GroupListPresenceTally.ofStates states)

def ResolvedGroupListOperands.evalAddressedTally
    (context : AddressedValidationEvaluationContext model) :
    List (ResolvedGroupListOperand model) →
      Except CheckedAddressingError GroupListPresenceTally
  | [] => pure { filled := 0, empty := 0, unavailable := 0 }
  | operand :: remaining => do
      pure ((← operand.evalAddressedTally context).add
        (← evalAddressedTally context remaining))

namespace ValidationConditionLeaf

def canFireOnEmpty : ValidationConditionLeaf model → Bool
  | .flat condition => condition.canFireOnEmpty
  | .numeric _ _ | .orderedNumeric _ _ => false
  | .groupPresence operator _ => operator.canFireOnEmpty
  | .groupList operator _ => operator.canFireOnEmpty
  | .repeatableFieldPresence operator _ => operator.canFireOnEmpty
  | .repetitionNotUnique _ => false

def referencesField : ValidationConditionLeaf model → FieldId → Bool
  | .flat condition, field => condition.referencesField field
  | .numeric _ comparison, field => comparison.referencesField model field
  | .orderedNumeric _ comparison, field =>
      comparison.referencesField field
  | .groupPresence _ reference, field => reference.referencesField model field
  | .groupList _ operands, field =>
      operands.any fun operand => operand.referencesField field
  | .repeatableFieldPresence _ declaration, field =>
      declaration.id == field
  | .repetitionNotUnique source, field =>
      source.referencesField field

/-- Whether a leaf retains any `Having` filter in its checked source. Only the model-indexed ordered numeric carrier can currently own such a source; scalar leaves cannot manufacture the marker. -/
def hasHaving : ValidationConditionLeaf model → Bool
  | .orderedNumeric _ comparison => comparison.hasHaving
  | .flat _ | .numeric _ _ | .groupPresence _ _ | .groupList _ _
  | .repeatableFieldPresence _ _ | .repetitionNotUnique _ => false

/-- Whether this leaf retains a repeatable numeric source and therefore cannot use the scalar checked evaluator. -/
def requiresAddressedValidation : ValidationConditionLeaf model → Bool
  | .orderedNumeric _ comparison =>
      comparison.requiresAddressedValidation
  | .groupPresence _ reference =>
      !(model.repeatableScopeForGroupPath reference.path).isEmpty
  | .groupList _ operands =>
      operands.any ResolvedGroupListOperand.isStarred
  | .repeatableFieldPresence _ _ => true
  | .repetitionNotUnique _ => true
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
      reference.presenceWellFormedBool model rowGroup
  | .groupList operator operands =>
      ResolvedGroupListOperands.wellFormedBool operator operands rowGroup
  | .repeatableFieldPresence _ declaration =>
      match model.lookupUniqueId declaration.id with
      | .ok checked =>
          checked == declaration && !declaration.repeatableScope.isEmpty
      | .error _ => false
  | .repetitionNotUnique source =>
      source.wellFormedBool rowGroup

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
      match operands.mapM fun operand =>
          operand.evalDirectPresence? context isRelevant with
      | some states =>
          (operator.evalPresence states).asConservativeVerdict
      | none => .unknown
  | .repeatableFieldPresence _ _ => .unknown
  | .repetitionNotUnique _ => .unknown

/-- Whether a leaf has an exact partial addressed interpretation. `false` is structural unsupported information and must not be converted to semantic UNKNOWN. -/
def supportsAddressedPartial : ValidationConditionLeaf model → Bool
  | .flat _ | .repeatableFieldPresence _ _ => true
  | .orderedNumeric _ comparison =>
      comparison.supportsAddressedPartial
  | _ => false

/-- Evaluate one partial addressed leaf. `none` is structural unsupported information, not semantic UNKNOWN; a reached but nonrelevant supported source returns the family's exact UNKNOWN result. -/
def evalAddressedPartial?
    (context : AddressedValidationEvaluationContext model)
    (scope : ValidationRelevanceScope)
    (isRelevant : FlatRelevance) :
    ValidationConditionLeaf model →
      Option (Except CheckedAddressingError Verdict)
  | .flat condition =>
      some (pure (condition.evalSelected context.scalar.fields isRelevant))
  | .repeatableFieldPresence operator declaration =>
      some (if isRelevant declaration.id then
        context.readCell context.outer declaration.id |>.map fun cell =>
          operator.eval (observeCell .validation cell)
      else
        pure .unknown)
  | .orderedNumeric _ comparison =>
      comparison.evalAddressedPartial? context scope isRelevant
  | _ => none

/-- Evaluate one addressed leaf through the same relevance rules. Ordered numeric and starred group-list sources preserve structural addressing failures; direct scalar/group leaves remain the exact pure evaluator lifted into that channel. -/
def evalAddressed (context : AddressedValidationEvaluationContext model) :
    ValidationConditionLeaf model → Except CheckedAddressingError Verdict
  | .orderedNumeric _ comparison => comparison.evalAddressed context
  | .groupList operator operands => do
      pure (operator.evalTally
        (← ResolvedGroupListOperands.evalAddressedTally
          context operands)).asConservativeVerdict
  | .groupPresence operator reference =>
      match context.input with
      | .legacy _ _ =>
          let leaf : ValidationConditionLeaf model :=
            .groupPresence operator reference
          pure (leaf.evalSelected context.scalar context.directRelevant)
      | .checked document => do
          let input ←
            (document.groupPresenceInput reference.path context.outer
              .fullyRelevant false).mapError .group
          pure (operator.eval input.derive)
  | .repeatableFieldPresence operator declaration => do
      pure (operator.eval
        (observeCell .validation
          (← context.readCell context.outer declaration.id)))
  | .repetitionNotUnique _ =>
      .error (.repetitionNotUniqueResult context.outer)
  | leaf => pure (leaf.evalSelected context.scalar context.directRelevant)

/-- Evaluate one reached leaf with the rule-owned current-row RNU result. Every other leaf delegates to the established addressed evaluator unchanged. -/
def evalAddressedWithRepetitionNotUnique
    (context : AddressedValidationEvaluationContext model)
    (result? : Option RepetitionNotUniqueResult) :
    ValidationConditionLeaf model → Except CheckedAddressingError Verdict
  | .repetitionNotUnique _ =>
      match result? with
      | some result =>
          if result.row == context.outer then
            pure result.verdict
          else
            .error (.repetitionNotUniqueResult context.outer)
      | none => .error (.repetitionNotUniqueResult context.outer)
  | leaf => leaf.evalAddressed context

end ValidationConditionLeaf

namespace ValidationCondition

def canFireOnEmpty (condition : ValidationCondition model) : Bool :=
  condition.evalBool ValidationConditionLeaf.canFireOnEmpty

def referencesField (condition : ValidationCondition model)
    (field : FieldId) : Bool :=
  condition.anyLeaf fun leaf => leaf.referencesField field

/-- The checked condition retains at most one RNU source; exposing it lets the ordinary rule prepare the branch-independent relation before the connective walk. -/
def repetitionNotUniqueSources
    (condition : ValidationCondition model) :
    List (CheckedRepetitionNotUniqueSource model) :=
  match condition with
  | .leaf (.repetitionNotUnique source) => [source]
  | .leaf _ => []
  | .and left right | .or left right =>
      repetitionNotUniqueSources left ++ repetitionNotUniqueSources right

def repetitionNotUniqueSource?
    (condition : ValidationCondition model) :
    Option (CheckedRepetitionNotUniqueSource model) :=
  condition.repetitionNotUniqueSources.head?

end ValidationCondition

end A12Kernel
