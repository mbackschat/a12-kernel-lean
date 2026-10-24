import A12Kernel.Elaboration.IterationGuard
import A12Kernel.Elaboration.KeyedGroupPresence
import A12Kernel.Elaboration.CustomCondition
import A12Kernel.Elaboration.StringExpression
import A12Kernel.Elaboration.NumericValidation
import A12Kernel.Elaboration.CheckedGroupPresence
import A12Kernel.Elaboration.RepetitionNotUnique
import A12Kernel.Elaboration.SingleGroup
import A12Kernel.Elaboration.StarGroup
import A12Kernel.Elaboration.ValidationContext
import A12Kernel.Elaboration.CurrentRepetition
import A12Kernel.Elaboration.IteratedDateRangeCondition
import A12Kernel.Elaboration.CustomFieldValidity
import A12Kernel.Elaboration.IndexedStringPattern
import A12Kernel.Elaboration.StringPattern
import A12Kernel.Elaboration.ValueListCondition
import A12Kernel.Elaboration.ValuesNotUniqueCondition
import A12Kernel.Elaboration.FirstFilledComparison
import A12Kernel.Elaboration.TokenComparison
import A12Kernel.Elaboration.TemporalExpression

/-! # Shared resolved validation conditions

This boundary joins checked semantic leaves under one connective tree. It accepts only leaf-family certificates produced by their owning elaborators and never reconstructs them from unchecked data.
-/

/-! This focused module owns resolved validation-condition leaves, connective evaluation, and dependency discovery. Static iteration scope lives in `StaticIteration`. -/

namespace A12Kernel

/-- One authored operand of the kernel's group-list condition family. Despite the language-level name, the checked entity list admits fields, ordinary groups, and — for two operators — groups below starred repeatable ancestry. -/
inductive SurfaceGroupListOperand where
  | indexed (source : SurfaceSemanticIndex)
  | keyed (source : SurfaceKeyedEntityExtent)
  | field (reference : SurfaceFieldPath)
  | group (reference : SurfaceGroupReference)
  | starredGroup (reference : SurfaceStarGroupPath)
  deriving Repr, DecidableEq

/-- A group-list operand after model-owned resolution. Every variant retains its exact declaration or checked source, so overlap, topology, and checked-core coherence cannot be forged from paths alone. -/
inductive ResolvedGroupListOperand (model : FlatModel) where
  | indexed (source : CheckedSemanticIndexSource model)
  | keyed (source : CheckedKeyedEntityExtent model)
  | field (declaration : FlatFieldDecl)
  | group (reference : ResolvedGroupReference)
  | starredGroup (source : CheckedStarredGroupSource model)
  | starredGroupPresence (source : CheckedStarredGroupPresenceSource model)

namespace ResolvedGroupListOperand

def entityPath : ResolvedGroupListOperand model → List String
  | .indexed source => source.targetDeclaration.path
  | .keyed source => source.entityPath
  | .field declaration => declaration.path
  | .group reference => reference.path
  | .starredGroup source => source.group.path
  | .starredGroupPresence source => source.groupPath

def isRootGroup : ResolvedGroupListOperand model → Bool
  | .indexed _ | .keyed _ => false
  | .field _ => false
  | .group reference => reference.isRoot
  | .starredGroup source => source.group.path.length == 1
  | .starredGroupPresence source => source.groupPath.length == 1

def isStarred : ResolvedGroupListOperand model → Bool
  | .indexed _ => false
  | .keyed source => source.isStarredGroup
  | .starredGroup _ | .starredGroupPresence _ => true
  | .field _ | .group _ => false

def referencesField (operand : ResolvedGroupListOperand model)
    (field : FieldId) : Bool :=
  match operand with
  | .indexed source => source.referencesField field
  | .keyed source => source.referencesField field
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

/-- A starred source is rechecked at the lexical group it was resolved from, which an error-field
binding leaves in place; a fixed group is rechecked at the binding. -/
def wellFormedBool (operand : ResolvedGroupListOperand model)
    (rowGroup : GroupPath) (declaringGroup : GroupPath := rowGroup) : Bool :=
  match operand with
  | .indexed _ => true
  | .keyed source => source.isGroup
  | .field declaration =>
      match model.lookupUniqueId declaration.id with
      | .ok checked =>
          checked == declaration &&
            declaration.repeatableScope.isPrefixOf (model.repeatableScopeForGroupPath rowGroup)
      | .error _ => false
  | .group reference =>
      reference.fixedWellFormedBool model rowGroup
  | .starredGroup source => source.wellFormedBool declaringGroup
  | .starredGroupPresence source => source.wellFormedBool declaringGroup

private def overlapsStarred (path : GroupPath) :
    ResolvedGroupListOperand model → Bool
  | .indexed _ | .keyed _ => false
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

def indexIdentity? : ResolvedGroupListOperand model → Option (GroupPath × CheckedSemanticIndexKey)
  | .indexed source => some (source.group.path, source.key)
  | .keyed source => some (source.selection.group.path, source.selection.key)
  | _ => none

/-- Kernel entity-list duplicate checking rejects direct non-wildcard duplicates and every strict group/descendant pair. Repeated starred operands and unrelated siblings remain independent authored occurrences. -/
def overlaps (left right : ResolvedGroupListOperand model) : Bool :=
  if left.indexIdentity? != right.indexIdentity? then false else
  match left with
  | .indexed _ | .keyed _ =>
      if left.isStarred && right.isStarred && left.entityPath == right.entityPath then false
      else left.entityPath.isPrefixOf right.entityPath || right.entityPath.isPrefixOf left.entityPath
  | .field leftDeclaration =>
      match right with
      | .indexed _ | .keyed _ => false
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
      | .indexed _ | .keyed _ => false
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

/-- The repeatable scope already bound by a fixed child, or the captured repeatable prefix of a
starred group operand. Ordinary scalar operands contribute no rule-iteration scope. -/
def iterationScope :
    ResolvedGroupListOperand model → Option (List RepeatableLevel)
  | .group reference =>
      let scope := reference.boundRepeatableScope
      if scope.isEmpty then none else some scope
  | .starredGroup source =>
      let scope := source.path.bindingScope
      if scope.isEmpty then none else some scope
  | .starredGroupPresence source =>
      let scope := source.path.bindingScope
      if scope.isEmpty then none else some scope
  | .field declaration =>
      let scope := declaration.repeatableScope
      if scope.isEmpty then none else some scope
  | .indexed _ | .keyed _ => none

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
    (rowGroup : GroupPath) (declaringGroup : GroupPath := rowGroup) : Bool :=
  !operands.isEmpty &&
    (if operator.requiresMultipleOperands then
      1 < operands.length &&
        !operands.any ResolvedGroupListOperand.isStarred
    else
      operands.length != 1 ||
        operands.any ResolvedGroupListOperand.isStarred) &&
    operands.all (·.wellFormedBool rowGroup declaringGroup) &&
    (firstOverlap? operands).isNone &&
    (!operands.any ResolvedGroupListOperand.isRootGroup ||
      (!operator.requiresMultipleOperands && operands.length == 1))

end ResolvedGroupListOperands



/-- The validation leaf families admitted by this checked condition boundary, indexed by the one model that owns every retained source certificate. -/
inductive ValidationConditionLeaf (model : FlatModel) where
  | keyedGroupPresence (operator : GroupPresenceOperator) (source : CheckedKeyedEntityExtent model)
  | indexedFieldPresence (operator : RepeatableFieldPresenceOperator) (source : CheckedSemanticIndexSource model)
  | customCondition (name : CheckedCustomConditionName)
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
  | guardedRootCurrentRepetition
      (guard : FlatFieldDecl) (group : GroupPath)
      (comparison : RootCurrentRepetitionComparison)
  | guardedRepeatableCurrentRepetition
      (guard : FlatFieldDecl)
      (source : CheckedCurrentRepetitionSource model)
      (comparison : RepeatableCurrentRepetitionComparison)
  | iteratedDateRange (condition : IteratedDateRangeCondition model)
  /-- An explicit `Valid`/`Invalid` predicate over a registered custom type. The operand is a single
  nonrepeatable field, so this leaf reads like a flat one and carries no iteration of its own. -/
  | customFieldValidity (leaf : CheckedCustomFieldValidityLeaf model)
  | indexedCustomFieldValidity (leaf : CheckedIndexedCustomFieldValidityLeaf model)
  /-- One of the seven field-fill quantifiers over a field-fill list. The leaf is
  not a projection of `NumberOfFilledFields`: a formally invalid cell leaves the count unavailable
  while `AtLeastOneFieldFilled` still fires on a filled sibling. -/
  | fieldFill (operator : FieldFillQuantifier) (source : CheckedFieldFillList model)
  /-- `PatternMatched` or `PatternViolated` over one ordinary nonrepeatable String field, read like a
  flat leaf through the field's validation-phase String. -/
  | stringPattern (leaf : CheckedStringPatternLeaf model)
  | indexedStringPattern (leaf : CheckedIndexedStringPatternLeaf model)
  | valueList (source : CheckedValueListCondition model)
  | valuesNotUnique (source : CheckedValuesNotUniqueCondition model)
  | firstFilledComparison (comparison : CheckedFirstFilledComparison model)
  | tokenComparison (comparison : CheckedTokenComparison model)
  | stringExpression (comparison : CheckedStringExpressionComparison model)
  | scalarTemporal (comparison : CheckedScalarTemporalComparison model)
  | constructedDateValidity (operation : ConstructedDateValidityOp)
      (source : CheckedConstructedDateComponents model (ScalarDateComponent model))

/-- One checked connective tree whose leaves retain their family-specific resolved certificates and evaluation policies. -/
abbrev ValidationCondition (model : FlatModel) :=
  ConditionTree (ValidationConditionLeaf model)

/-- Static classification-pass eligibility follows the authored operator families, not the
runtime verdict or empty-document gate (`CodeGenHelper.canCreateOmissionErrors`). -/
private def numericClassificationSource : NumericValidationAtom → Bool
  | .fixedCurrentRepetition _ | .boundCurrentRepetition _ | .baseYear _ | .baseYearDatePart _ _ _ => false
  | .dateDifference _ left right | .dayDifference _ left right => left.isField || right.isField
  | .dateTimeDifference _ left right => !(left.fields ++ right.fields).isEmpty
  | .field _ | .temporalFieldPart _ _ _ | .dateRangeBoundPart _ _ _ | .stringLength _
  | .stringRange _ _ _ | .fieldValueAsNumber _ | .aggregate _ _ | .filledGroupCount _ => true

private def orderedNumericClassificationSource : OrderedNumericValidationAtom model → Bool
  | .indexed _ | .indexedString _ => true
  | .temporalExpression source => !source.fieldIds.isEmpty
  | .ordinary source => numericClassificationSource source
  | .firstFilled _ | .valueCount _ _ | .tokenValueCount _ | .booleanValueCount _
  | .aggregate _ _ | .sumOfProducts _ | .filledGroupCountMixed _ | .filledFieldCount _
  | .tokenDistinctCount _ | .temporalDistinctCount _ => true

/-- Preserve the generator's static distinction even for a leaf that happens to fire only value
messages on the current document. In particular a child-group presence guard enables the pass,
whereas unfiltered positive field presence does not (classification grid, 2026-10-04). -/
def ValidationConditionLeaf.requiresClassificationPass : ValidationConditionLeaf model → Bool
  | .customCondition _ => false
  | .flat (.compare comparison) => !comparison.fieldIds.isEmpty
  | .flat (.fieldFilled _) => false
  | .flat (.fieldNotFilled _) => true
  | .flat (.tokenValueList quantifier _ values form) =>
      match form with
      | .membership => !values.operands.isEmpty
      | .quantifier => quantifier != .atLeastOne
  | .flat (.numberValueList quantifier _ values form) =>
      match form with
      | .membership => !values.operands.isEmpty
      | .quantifier => quantifier != .atLeastOne
  | .numeric _ comparison =>
      comparison.left.anyAtom numericClassificationSource || comparison.right.anyAtom numericClassificationSource
  | .orderedNumeric _ comparison =>
      comparison.left.anyAtom orderedNumericClassificationSource || comparison.right.anyAtom orderedNumericClassificationSource
  | .groupPresence operator reference => !reference.isRoot || operator == .notFilled
  | .groupList operator operands =>
      !operands.any (·.isRootGroup) || operator == .noGroupFilled
  | .keyedGroupPresence _ _ => true
  | .indexedFieldPresence operator _ | .repeatableFieldPresence operator _ => operator == .notFilled
  | .repetitionNotUnique _ => true
  | .guardedRootCurrentRepetition _ _ _ | .guardedRepeatableCurrentRepetition _ _ _ => false
  | .iteratedDateRange (.pluralOverlap source) => source.hasHaving
  | .iteratedDateRange (.yearlessPluralOverlap source) => source.operands.any (·.hasFilter)
  | .iteratedDateRange _ => true
  | .customFieldValidity _ | .indexedCustomFieldValidity _ => false
  | .stringPattern _ | .indexedStringPattern _ => true
  | .fieldFill operator source =>
      match operator with
      | .allFieldsFilled | .moreThanOneFieldFilled => source.hasHaving
      | .noFieldFilled | .notAllFieldsFilled | .notExactlyOneFieldFilled
      | .atLeastOneFieldFilled | .fieldsNotCollectivelyFilled => true
  | .valueList source => source.quantifier != .atLeastOne || source.hasHaving
  | .valuesNotUnique source => source.hasHaving
  | .firstFilledComparison _ => true
  | .tokenComparison _ => true
  | .stringExpression comparison => !comparison.declarations.isEmpty
  | .scalarTemporal comparison => !comparison.fieldIds.isEmpty
  | .constructedDateValidity _ source => source.hasImmediateEntity

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

/-- Embed the exact measured nonrepeatable-root condition. The direct filled guard and closed comparison remain one indivisible leaf. -/
def guardedRootCurrentRepetition
    (guard : FlatFieldDecl) (group : GroupPath)
    (comparison : RootCurrentRepetitionComparison) :
    ValidationCondition model :=
  .leaf (.guardedRootCurrentRepetition guard group comparison)

/-- Embed one checked explicit validity predicate. The operand, the resolved type name, and the polarity travel together, so a tree can never pair an admitted operand with an unresolved name. -/
def customFieldValidity (leaf : CheckedCustomFieldValidityLeaf model) :
    ValidationCondition model :=
  .leaf (.customFieldValidity leaf)

/-- Embed the exact measured same-group repeatable condition. The filled guard, model-owned level, and closed comparison remain one leaf. -/
def guardedRepeatableCurrentRepetition
    (guard : FlatFieldDecl)
    (source : CheckedCurrentRepetitionSource model)
    (comparison : RepeatableCurrentRepetitionComparison) :
    ValidationCondition model :=
  .leaf (.guardedRepeatableCurrentRepetition guard source comparison)

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
  -- The scalar channel reads no row, so a row-bound field is unavailable on it.
  | .field declaration =>
      some (if isRelevant declaration.id && declaration.repeatableScope.isEmpty then
        (declaration.toPresenceField.observeValidation
          context.fields).asGroupListPresence
      else
        .unavailable)
  | .group reference =>
      some (match context.groups reference.path with
        | some state => state.asGroupListPresence
        | none => .unavailable)
  | .indexed _ | .keyed _ | .starredGroup _ | .starredGroupPresence _ => none

def ResolvedGroupListOperand.evalAddressedTally
    (context : AddressedValidationEvaluationContext model) :
    ResolvedGroupListOperand model →
      Except CheckedAddressingError GroupListPresenceTally
  | .indexed source => do
      let document ← match context.input with
        | .checked document => pure document
        | _ => throw (.checkedDocumentRequired source.group.path)
      pure (GroupListPresenceTally.ofStates [(← source.observeDocument document context.outer .validation).asGroupListPresence])
  | .keyed source => do
      let document ← match context.input with
        | .checked document => pure document
        | _ => throw (.checkedDocumentRequired source.groupPath)
      match ← source.validationGroupStates document context.outer with
      | none => pure (GroupListPresenceTally.ofStates [.unavailable])
      | some states => pure (GroupListPresenceTally.ofGroupStates states)
  | .field declaration => do
      if !context.directRelevant declaration.id then
        return GroupListPresenceTally.ofStates [.unavailable]
      if declaration.repeatableScope.isEmpty then
        return GroupListPresenceTally.ofStates
          [(declaration.toPresenceField.observeValidation context.scalar.fields).asGroupListPresence]
      pure (GroupListPresenceTally.ofStates
        [(observeCell .validation (← context.readCell context.outer declaration.id)).asGroupListPresence])
  | .group reference =>
      match context.input with
      | .legacy _ _ | .partialView _ _ =>
          pure (GroupListPresenceTally.ofStates [match context.scalar.groups
              reference.path with
            | some state => state.asGroupListPresence
            | none => .unavailable])
      | .checked document => do
          let input ←
            (document.groupPresenceInput reference.path context.outer
              .fullyRelevant false).mapError .group
          pure (GroupListPresenceTally.ofStates [input.derive.asGroupListPresence])
  | .starredGroup source => do
      let document := match context.input with
        | .legacy document _ => document
        | .checked checked => checked.source.toDocument
        | .partialView checked _ => checked.source.toDocument
      let count ←
        (source.inCapacityRowCount document context.outer).mapError .addressing
      pure (GroupListPresenceTally.filledOnly count)
  | .starredGroupPresence source =>
      match context.input with
      | .legacy _ _ => .error (.checkedDocumentRequired source.groupPath)
      | .checked document | .partialView document _ => do
          let environments ←
            (source.inCapacityEnvironments document.source.toDocument context.outer)
              |>.mapError .addressing
          let states ← environments.mapM fun environment => do
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

/-- Whether a count stands on the comparison's small side, the operand its error condition needs to
be small: the left of `<` and `<=`, the right of `>` and `>=`, either side of `==` and `!=`. The
count may sit anywhere inside that operation, beneath arithmetic or a function. The tolerance
comparisons take either side by the Kernel's source and are unmeasured. -/
private def countsOnSmallSide (comparison : NumericComparisonOf Atom) (isCount : Atom → Bool) : Bool :=
  let left := comparison.left.anyAtom isCount
  let right := comparison.right.anyAtom isCount
  match comparison.op with
  | .ordinary .less | .ordinary .lessEqual => left
  | .ordinary .greater | .ordinary .greaterEqual => right
  | .ordinary .equal | .ordinary .notEqual | .tolerance _ => left || right

/-- The counts the empty-instance gate looks for: `NumberOfFilledFields`, `NumberOfFilledGroups` and
`NumberOfDifferentValues`. -/
private def NumericValidationAtom.isEmptyGateCount : NumericValidationAtom → Bool
  | .filledGroupCount _ | .aggregate .distinctCount _ => true
  | _ => false

/-- Whether a comparison leaf lifts the empty-instance gate from wherever it stands in the
condition: a count on its small side, whatever else it reads, and not a count only on the large
side. Over a blank root the Kernel fires `NumberOfFilledGroups(G1, G2) + [W] < 2`, `2 > …`,
`== 0`, `!= 1`, `Abs(…) < 2`, `1 >= NumberOfFilledFields(A, W)`, `NumberOfFilledFields(A, W) <= 1`
and `NumberOfDifferentValues(A, W) < 1`, reading the empty `W` as `0`, and leaves `… >= 0`,
`0 <= …` and `[W] < 5` silent
([checkpoint](../../../docs/sources/group-list-and-capacity-probes.md#src-rule-bucket-empty-gate)).
The leaf lifts the gate beneath `And` too: `NumberOfFilledFields(A, W) < 1 And
NumberOfFilledFields(A, W) >= 0` fires there, so this test does not compose like the presence
test below ([checkpoint](../../../docs/sources/group-list-and-capacity-probes.md#src-empty-gate-count-beneath-and)). -/
def liftsEmptyGate : ValidationConditionLeaf model → Bool
  | .numeric _ comparison => countsOnSmallSide comparison NumericValidationAtom.isEmptyGateCount
  | .orderedNumeric _ comparison => countsOnSmallSide comparison fun
      | .ordinary atom => NumericValidationAtom.isEmptyGateCount atom
      | .filledGroupCountMixed _ | .filledFieldCount _ | .aggregate .distinctCount _
      | .tokenDistinctCount _ | .temporalDistinctCount _ => true
      | _ => false
  | _ => false

/-- Whether a presence leaf can hold on an instance without admitted content; it composes through
`And` and `Or`. A comparison claims nothing here, `liftsEmptyGate` owning it. -/
def canFireOnEmpty : ValidationConditionLeaf model → Bool
  | .customCondition _ => true
  | .constructedDateValidity operation source =>
      operation == .invalid || source.scalarFieldIds.isEmpty
  | .firstFilledComparison _ | .tokenComparison _ => false
  | .stringExpression _ | .scalarTemporal _ => false
  | .valuesNotUnique _ => false
  | .valueList source => source.quantifier.canFireOnEmpty
  | .flat condition => condition.canFireOnEmpty
  | .numeric _ _ | .orderedNumeric _ _ => false
  | .groupPresence operator _ => operator.canFireOnEmpty
  | .groupList operator _ => operator.canFireOnEmpty
  | .keyedGroupPresence operator _ => operator.canFireOnEmpty
  | .indexedFieldPresence operator _ | .repeatableFieldPresence operator _ => operator.canFireOnEmpty
  | .repetitionNotUnique _ => false
  | .guardedRootCurrentRepetition _ _ _ => false
  | .guardedRepeatableCurrentRepetition _ _ _ => false
  | .iteratedDateRange _ => false
  -- The value-specified gate answers UNKNOWN for an empty operand before any registry contact, so
  -- neither polarity of the explicit predicate can fire on one.
  | .customFieldValidity _ | .indexedCustomFieldValidity _ => false
  -- An empty operand is never matched, so neither operator fires on an empty instance.
  | .stringPattern _ | .indexedStringPattern _ => false
  | .fieldFill operator _ => match operator with
      | .noFieldFilled | .notAllFieldsFilled | .notExactlyOneFieldFilled => true
      | .allFieldsFilled | .atLeastOneFieldFilled | .moreThanOneFieldFilled
      | .fieldsNotCollectivelyFilled => false

def referencesField : ValidationConditionLeaf model → FieldId → Bool
  | .customCondition _, _ => false
  | .constructedDateValidity _ source, field => source.scalarFieldIds.contains field
  | .firstFilledComparison comparison, field => comparison.referencesField field
  | .tokenComparison comparison, field => comparison.referencesField field
  | .stringExpression comparison, field => comparison.referencesField field
  | .scalarTemporal comparison, field => comparison.referencesField field
  | .valuesNotUnique source, field => source.referencesField field
  | .valueList source, field => source.referencesField field
  | .flat condition, field => condition.referencesField field
  | .numeric _ comparison, field => comparison.referencesField model field
  | .orderedNumeric _ comparison, field =>
      comparison.referencesField field
  | .groupPresence _ reference, field => reference.referencesField model field
  | .groupList _ operands, field =>
      operands.any fun operand => operand.referencesField field
  | .keyedGroupPresence _ source, field => source.referencesField field
  | .indexedFieldPresence _ source, field => source.referencesField field
  | .repeatableFieldPresence _ declaration, field =>
      declaration.id == field
  | .repetitionNotUnique source, field =>
      source.referencesField field
  | .guardedRootCurrentRepetition guard _ _, field =>
      guard.id == field
  | .guardedRepeatableCurrentRepetition guard _ _, field =>
      guard.id == field
  | .iteratedDateRange condition, field => condition.referencesField field
  | .customFieldValidity leaf, field => leaf.operand.source == field
  | .indexedCustomFieldValidity leaf, field => leaf.source.selection.referencesField field
  | .fieldFill _ source, field => source.referencesField field
  | .stringPattern leaf, field => leaf.condition.referencesField field
  | .indexedStringPattern leaf, field => leaf.selection.referencesField field

/-- Whether a leaf reaches `field` for the rule's error-field gates. Filter-owning sources count
    marked body entities but exclude unmarked candidate references, following the shared correlation gate. -/
def referencesErrorField : ValidationConditionLeaf model → FieldId → Bool
  | .customCondition _, _ => false
  | .firstFilledComparison comparison, field => comparison.referencesField field (CorrelatedHaving.referencesMarkedEntityField model)
  | .tokenComparison comparison, field => comparison.referencesField field (CorrelatedHaving.referencesMarkedEntityField model)
  | .fieldFill _ source, field => source.referencesField field (CorrelatedHaving.referencesMarkedEntityField model)
  | .valuesNotUnique source, field => source.referencesField field (CorrelatedHaving.referencesMarkedEntityField model)
  | .valueList source, field => source.referencesField field (CorrelatedHaving.referencesMarkedEntityField model)
  | .orderedNumeric _ comparison, field => comparison.referencesErrorField field
  | .iteratedDateRange condition, field => condition.referencesErrorField field
  | .scalarTemporal comparison, field =>
      comparison.referencesWith field (fun condition => CorrelatedHaving.referencesMarkedEntityField model condition field)
  | .constructedDateValidity _ components, field =>
      components.scalarCore.referencesWith field (fun condition => CorrelatedHaving.referencesMarkedEntityField model condition field)
  | leaf@(.flat _), field | leaf@(.numeric _ _), field | leaf@(.groupPresence _ _), field
  | leaf@(.keyedGroupPresence _ _), field
  | leaf@(.indexedFieldPresence _ _), field
  | leaf@(.groupList _ _), field | leaf@(.repeatableFieldPresence _ _), field
  | leaf@(.repetitionNotUnique _), field | leaf@(.guardedRootCurrentRepetition _ _ _), field
  | leaf@(.guardedRepeatableCurrentRepetition _ _ _), field
  | leaf@(.customFieldValidity _), field | leaf@(.indexedCustomFieldValidity _), field
  | leaf@(.stringPattern _), field | leaf@(.indexedStringPattern _), field | leaf@(.stringExpression _), field =>
      leaf.referencesField field

/-- Whether the checked source retains a `Having` filter, which makes whole-rule partial validation
    skip before evaluation (spec/10 §5). Scalar leaves cannot manufacture the marker. -/
def hasHaving : ValidationConditionLeaf model → Bool
  | .customCondition _ => false
  | .firstFilledComparison comparison => comparison.hasHaving
  | .tokenComparison comparison => comparison.hasHaving
  | .fieldFill _ source => source.hasHaving
  | .constructedDateValidity _ source => source.scalarCore.hasHaving
  | .scalarTemporal source => source.left.core.hasHaving || source.right.core.hasHaving
  | .stringExpression _ => false
  | .valuesNotUnique source => source.hasHaving
  | .valueList source => source.hasHaving
  | .orderedNumeric _ comparison => comparison.hasHaving
  | .iteratedDateRange condition => !condition.filters.isEmpty
  | .flat _ | .numeric _ _ | .groupPresence _ _ | .groupList _ _
  | .keyedGroupPresence _ _ | .indexedFieldPresence _ _ | .repeatableFieldPresence _ _ | .repetitionNotUnique _
  | .guardedRootCurrentRepetition _ _ _
  | .guardedRepeatableCurrentRepetition _ _ _
  | .customFieldValidity _ | .indexedCustomFieldValidity _ | .stringPattern _ | .indexedStringPattern _ => false

/-- Whether this leaf needs an addressed context rather than the scalar checked evaluator. -/
def requiresAddressedValidation : ValidationConditionLeaf model → Bool
  | .flat condition => model.fields.any fun field =>
      condition.referencesField field.id && !field.repeatableScope.isEmpty
  | .customCondition _ | .indexedCustomFieldValidity _ | .indexedStringPattern _ => true
  | .customFieldValidity leaf => !leaf.operand.declaration.repeatableScope.isEmpty
  | .stringPattern leaf => !(model.fieldRepeatableScope leaf.condition.field.id).isEmpty
  | .constructedDateValidity _ _ | .stringExpression _ => true
  | .scalarTemporal comparison => comparison.left.requiresAddressed || comparison.right.requiresAddressed ||
      comparison.bindingScopes.any (fun scope => !scope.isEmpty)
  | .firstFilledComparison _ | .tokenComparison _ | .valueList _ | .valuesNotUnique _ => true
  | .orderedNumeric _ comparison =>
      comparison.requiresAddressedValidation
  | .groupPresence _ reference =>
      !(model.repeatableScopeForGroupPath reference.path).isEmpty
  | .groupList _ operands =>
      operands.any fun operand =>
        operand.indexIdentity?.isSome || operand.isStarred || operand.iterationScope.isSome
  | .keyedGroupPresence _ _ | .indexedFieldPresence _ _ | .repeatableFieldPresence _ _ => true
  | .repetitionNotUnique _ => true
  | .guardedRootCurrentRepetition _ _ _ => false
  | .guardedRepeatableCurrentRepetition _ _ _ => true
  | .iteratedDateRange _ => true
  | .fieldFill _ _ => true
  | _ => false

/-- Static admission reuses each leaf family's existing checked core predicate. -/
def wellFormedBool (rowGroup : GroupPath) (declaringGroup : GroupPath := rowGroup) :
    ValidationConditionLeaf model → Bool
  | .customCondition _ => true
  | .constructedDateValidity _ source => source.scalarBindingScopes.all
      (·.isPrefixOf (model.repeatableScopeForGroupPath rowGroup))
  | .firstFilledComparison comparison => comparison.bindingScopes.flatten.all
      (model.repeatableScopeForGroupPath rowGroup).contains
  | .tokenComparison comparison => comparison.bindingScopes.flatten.all
      (model.repeatableScopeForGroupPath rowGroup).contains
  | .stringExpression comparison => comparison.bindingScopes.all (·.isPrefixOf (model.repeatableScopeForGroupPath rowGroup))
  | .scalarTemporal comparison =>
      comparison.bindingScopes.all (·.isPrefixOf (model.repeatableScopeForGroupPath rowGroup))
  | .valuesNotUnique source => source.admittedMultiplicity && source.bindingScopes.flatten.all
      (model.repeatableScopeForGroupPath rowGroup).contains
  | .valueList source => source.bindingScopes.flatten.all
      (model.repeatableScopeForGroupPath rowGroup).contains
  | .flat condition =>
      if condition.isScalarMembership || (match condition with
          | .compare (.string ..) | .compare (.textFields ..) | .compare (.enumeration ..)
          | .compare (.boolean ..) | .compare (.confirm ..) | .compare (.booleanFields ..) => true
          | _ => false) then
        let scope := model.repeatableScopeForGroupPath rowGroup
        condition.wellFormedInBool model scope && model.fields.all (fun field =>
          !condition.referencesField field.id ||
            (model.unboundReadLevel? declaringGroup rowGroup field.repeatableScope scope).isNone)
      else condition.wellFormedBool model
  | .numeric scope comparison =>
      comparison.wellFormedInBool model rowGroup scope
  | .orderedNumeric scope comparison =>
      comparison.wellFormedInBool rowGroup scope
  | .groupPresence _ reference =>
      reference.presenceWellFormedBool model rowGroup
  | .groupList operator operands =>
      ResolvedGroupListOperands.wellFormedBool operator operands rowGroup declaringGroup
  | .keyedGroupPresence _ source => source.isGroup && !source.isStarredGroup &&
      source.bindingScopes.all (·.isPrefixOf (model.repeatableScopeForGroupPath rowGroup))
  | .indexedFieldPresence _ source => source.bindingScopes.all (·.isPrefixOf (model.repeatableScopeForGroupPath rowGroup))
  | .repeatableFieldPresence _ declaration =>
      match model.lookupUniqueId declaration.id with
      | .ok checked =>
          checked == declaration && !declaration.repeatableScope.isEmpty
      | .error _ => false
  | .repetitionNotUnique source =>
      source.wellFormedBool declaringGroup
  | .guardedRootCurrentRepetition guard group _ =>
      group == rowGroup && group.length == 1 &&
        model.hasGroupPath group &&
        (model.repeatableScopeForGroupPath group).isEmpty &&
        guard.groupPath == group && guard.repeatableScope.isEmpty &&
        match model.lookupUniqueId guard.id with
        | .ok checked => checked == guard
        | .error _ => false
  | .iteratedDateRange condition =>
      condition.wellFormedIn (model.repeatableScopeForGroupPath rowGroup)
  | .guardedRepeatableCurrentRepetition guard source _ =>
      guard.groupPath == source.path &&
        guard.repeatableScope.getLast? == some source.group.level &&
        match model.lookupUniqueId guard.id with
        | .ok checkedGuard => checkedGuard == guard
        | .error _ => false
  | .customFieldValidity leaf =>
      leaf.operand.declaration.repeatableScope.isPrefixOf (model.repeatableScopeForGroupPath rowGroup)
  | .indexedCustomFieldValidity leaf => leaf.source.bindingScopes.all (·.isPrefixOf (model.repeatableScopeForGroupPath rowGroup))
  -- The rule's row must bind every level the operand leaves unstarred above its own depth.
  | .fieldFill _ source =>
      source.bindingScope.all (model.repeatableScopeForGroupPath rowGroup).contains
  | .indexedStringPattern leaf => leaf.bindingScopes.all (·.isPrefixOf (model.repeatableScopeForGroupPath rowGroup))
  | .stringPattern leaf => model.admitsStringPatternField leaf.condition.field &&
      (model.fieldRepeatableScope leaf.condition.field.id).isPrefixOf (model.repeatableScopeForGroupPath rowGroup)


end ValidationConditionLeaf

namespace ValidationCondition

def referencesField (condition : ValidationCondition model)
    (field : FieldId) : Bool :=
  condition.anyLeaf fun leaf => leaf.referencesField field

private def numericStructuralGroups : NumericValidationAtom → List GroupPath
  | .fixedCurrentRepetition reference => [reference.path]
  | .boundCurrentRepetition source => [source.path]
  | .filledGroupCount groups => groups.map (·.path)
  | _ => []

private def orderedNumericStructuralGroups : OrderedNumericValidationAtom model → List GroupPath
  | .ordinary source => numericStructuralGroups source
  | .filledGroupCountMixed operands => operands.map (·.groupPath)
  | .filledFieldCount source => source.operands.map (·.groupPath)
  | _ => []

/-- Group-only sources retain root identity even when they read no field, as a repetition coordinate
or an empty declared group does. Ordinary field sources are covered by the existing read inventory. -/
private def structuralGroups : ValidationCondition model → List GroupPath
  | .leaf (.numeric _ comparison) =>
      (comparison.left.atoms ++ comparison.right.atoms).flatMap numericStructuralGroups
  | .leaf (.orderedNumeric _ comparison) =>
      (comparison.left.atoms ++ comparison.right.atoms).flatMap orderedNumericStructuralGroups
  | .leaf (.groupPresence _ reference) => [reference.path]
  | .leaf (.groupList _ operands) => operands.map (·.entityPath)
  | .leaf (.guardedRootCurrentRepetition _ group _) => [group]
  | .leaf (.guardedRepeatableCurrentRepetition _ source _) => [source.path]
  | .leaf (.fieldFill _ source) => source.operands.map (·.groupPath)
  | .leaf _ => []
  | .and left right | .or left right => structuralGroups left ++ structuralGroups right

/-- Roots named by the retained field inventory and structural group operands. This is static
membership, including unreached connective branches, never a scan of document content. Explicit
root-instance indices and reference forms omitted by a leaf's inventory are outside this projection. -/
def referencedRoots (condition : ValidationCondition model) : List String :=
  ((model.fields.filterMap fun declaration =>
    if condition.referencesField declaration.id then declaration.groupPath.head? else none) ++
    (structuralGroups condition).filterMap List.head?).eraseDups

/-- A second referenced root lifts full validation's content gate (spec/03 A.4). Merely declaring or
filling a second root does not: the projection reads the checked condition, not the document. -/
def referencesMultipleRoots (condition : ValidationCondition model) : Bool :=
  condition.referencedRoots.length > 1

/-- Whether the rule is evaluated without admitted content under full validation: its presence
leaves can hold there, a count lifts the gate, or its retained references span roots. -/
def canFireOnEmpty (condition : ValidationCondition model) : Bool :=
  condition.evalBool ValidationConditionLeaf.canFireOnEmpty ||
    condition.anyLeaf ValidationConditionLeaf.liftsEmptyGate || condition.referencesMultipleRoots

/-- Whether the condition references the rule's error field: a reference outside every filter body,
    or a `$`-marked one inside ([inbound](../../../docs/sources/inbound-handbacks.md#inbound-2026-09-26d-reference-set)). -/
def referencesErrorField (condition : ValidationCondition model)
    (field : FieldId) : Bool :=
  condition.anyLeaf fun leaf => leaf.referencesErrorField field

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
