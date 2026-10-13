import A12Kernel.Elaboration.ValidationCondition.Core

/-! Error-field membership and error-field iteration are distinct static obligations (spec/07 §1).
A selected payload can name the error field without binding an ordinary iteration level. This
projection retains that distinction across the checked callers without borrowing another
operand's scope. -/

namespace A12Kernel.ValidationCondition

private inductive ReferenceKind where
  | membership
  | nonFormMembership
  | iteration (level : RepeatableLevel)
  | nonIteration (level : RepeatableLevel)
  | nonWildcard (level : RepeatableLevel)
  | unkeyed (level : RepeatableLevel)
  | selected (group : GroupPath) (key : Option CheckedSemanticIndexKey)
  /-- A reference that is not a semantic-index selection of the queried field. -/
  | unselected
  /-- A reference binding every level of `scope`, the queried field's own repeatable scope: one
  written without a wildcard on any of them. -/
  | unstarred (scope : List RepeatableLevel)

/-- Error-field membership expands a group, but message index ancestry follows the authored
entity path (ReferencedIdsUtil.createAllIndexFieldEntityIds). The optional path restriction
keeps that distinction in the shared visitor without changing error-field membership. -/
private structure ReferenceQuery where
  kind : ReferenceKind
  within : Option GroupPath := none

private def ReferenceQuery.acceptsPath (query : ReferenceQuery) (path : GroupPath) : Bool :=
  query.within.all (·.isPrefixOf path)

private def ReferenceQuery.acceptsSlot (query : ReferenceQuery) : HavingFieldListSlot Ref → Bool
  | .direct _ => true
  | .extent source _ => query.acceptsPath source.groupPath

private def ReferenceQuery.binds (query : ReferenceQuery) (scope : List RepeatableLevel) (isForm : Bool := false) : Bool :=
  match query.kind with
  | .membership => true
  | .nonFormMembership => !isForm
  | .iteration level => scope.contains level
  | .nonIteration level => !scope.contains level
  | .nonWildcard level => scope.contains level
  | .unkeyed _ => true
  | .selected _ _ => false
  | .unselected => true
  | .unstarred fieldScope => fieldScope.all scope.contains

private def ReferenceQuery.atPath (query : ReferenceQuery) (path : GroupPath)
    (scope : List RepeatableLevel) (isForm : Bool := false) : Bool :=
  query.acceptsPath path && query.binds scope isForm

def sameMessageKey : CheckedSemanticIndexKey → CheckedSemanticIndexKey → Bool
  | .literal left _, .literal right _ => left == right
  | .field left, .field right => left.id == right.id
  | _, _ => false

/-- Static error references follow authored entities, not implicit index-cache reads
(EntityRefUtils.getDRefs/getGRefs; IterationChecker.checkIteration4NotOnlyVRefs).
Selection replaces its own iteration coordinate; a dynamic key keeps its independent scope. -/
private def selectedReferenceAt (field : FieldId) (query : ReferenceQuery)
    (source : Sum (CheckedSemanticIndexSource model) (CheckedKeyedEntityExtent model)) : Bool :=
  let selection := match source with | .inl source => source | .inr source => source.selection.indexSource
  let declarations := match source with | .inl source => [source.targetDeclaration] | .inr source => source.declarations
  let isForm := match source with
    | .inl _ => false
    | .inr source => match source.target with
        | .group path | .starredGroup path => path.length == 1
        | .star _ => false
  let path := match source with
    | .inl source => source.targetDeclaration.path
    | .inr source => source.entityPath
  let target := query.acceptsPath path && declarations.any (·.id == field) && match query.kind with
    | .selected group key => selection.group.path == group &&
        key.all (sameMessageKey selection.key)
    | .unkeyed level => selection.group.level != level
    | .nonWildcard level => selection.group.level == level ||
        selection.indexDeclaration.repeatableScope.dropLast.contains level
    | .unselected => false
    -- A selection replaces the selected level's wildcard; only a star written below it remains.
    -- Unmeasured on this carrier: the retained star-gate rows read the field without a key.
    | .unstarred _ => match source with
        | .inl _ => true
        | .inr source => match source.target with
            | .group _ => true
            | .starredGroup _ | .star _ => false
    | _ => query.binds selection.indexDeclaration.repeatableScope.dropLast isForm
  let key := match selection.key with
    | .literal .. => false
    | .field declaration => declaration.id == field && query.atPath declaration.path declaration.repeatableScope
  target || key

private def anyReference (answers : List (Option Bool)) : Option Bool :=
  if answers.contains (some true) then some true
  else if answers.contains none then none else some false

private def isFormSlot : HavingFieldListSlot HavingPresenceRef → Bool
  | .extent (.group reference) _ => reference.isRoot
  | .extent (.starredGroup path _) _ => path.length == 1
  | _ => false

/-- Marking preserves the authored extent's scope; group membership does not bind its descendants
(IterationChecker.checkIteration4NotOnlyVRefs; spec/07 §1). -/
private def markedRepetitionReferenceAt (model : FlatModel) (field : FieldId)
    (query : ReferenceQuery) (reference : HavingRepetitionRef) : Bool :=
  if reference.origin != .outer then false
  else
    (reference.groupPath? model).any fun path =>
      let group : ResolvedGroupReference := { path, origin := .path }
      group.referencesField model field &&
        query.atPath path (model.repeatableScopeForGroupPath path) group.isRoot

private def markedReferenceAt (model : FlatModel) (field : FieldId) (query : ReferenceQuery) :
    CorrelatedHaving → Bool
  | .and left right | .or left right =>
      markedReferenceAt model field query left || markedReferenceAt model field query right
  | .leaf leaf =>
      let slots : List (HavingFieldListSlot HavingPresenceRef) := match leaf with
        | .numeric comparison => (comparison.left.atoms ++ comparison.right.atoms).flatMap fun atom =>
            atom.presenceSlotsWith (fun source _ => source.presenceSlots)
        | .stringExpression comparison => comparison.presenceSlots
        | .selectedComparison comparison => comparison.presenceSlots
        | .temporalExpression comparison => comparison.presenceSlots
        | .dateValidity _ source => source.asTemporal.presenceSlots
        | .dateRange source => source.presenceSlots
        | .uniqueness source => source.presenceSlots
        | .fieldMembership _ source => source.presenceSlots
        | .fieldFill _ slots => slots
        | .groupFill _ first rest => (first :: rest).map (·.presenceSlot)
        | .groupPresence _ origin source =>
            [.extent (.group source.reference) (source.members.map fun member => { origin, field := member })]
        | _ => (CorrelatedHaving.markedFieldIds (.leaf leaf)).map fun member =>
            .direct { origin := .outer, field := member }
      (CorrelatedHaving.markedRepetitionReferences (.leaf leaf)).any (markedRepetitionReferenceAt model field query) || slots.any fun slot =>
        query.acceptsSlot slot && slot.references.any (fun reference => reference.origin == .outer && reference.field == field) &&
          match query.kind with
          | .membership => true
          | .nonFormMembership => !isFormSlot slot
          | .iteration level => (slot.outerIterationScope? model).any (·.contains level)
          | .nonIteration level => (slot.outerIterationScope? model).any (!·.contains level)
          | .nonWildcard level => (slot.outerIterationScope? model).any (·.contains level)
          | .unkeyed _ => true
          | .selected _ _ => false
          | .unselected => true
          | .unstarred fieldScope =>
              (slot.outerIterationScope? model).any (fun scope => fieldScope.all scope.contains)

private def rawOperandReferenceAt? (field : FieldId) (query : ReferenceQuery)
    (operand : ResolvedFieldEntityOperand model) : Option Bool :=
  match operand with
  | .indexed source => some (selectedReferenceAt field query (.inl source))
  | .keyed source => some (selectedReferenceAt field query (.inr source))
  | _ =>
      if !operand.expansionDeclarations.any (·.id == field) then some false
      else some (query.atPath operand.entityPath operand.bindingScope (operand.subtreePath?.any (fun path => path.length == 1)))

private def shapeReferenceAt? (field : FieldId) (query : ReferenceQuery)
    (shape : CheckedFieldEntityShape model) (filters : List CorrelatedHaving := []) : Option Bool :=
  anyReference (some (filters.any (markedReferenceAt model field query)) ::
    shape.operands.map (rawOperandReferenceAt? field query))

private def numberReferenceAt? (field : FieldId) (query : ReferenceQuery)
    (source : CheckedNumberEntitySource model) : Option Bool :=
  anyReference (source.operands.map fun
    | .field source => some (source.field.id == field && query.binds source.declaration.repeatableScope)
    | .star source => some (source.field.id == field && query.binds source.source.bindingScope)
    | .starHaving source => some ((source.source.field.id == field && query.binds source.source.source.bindingScope) ||
        markedReferenceAt model field query source.having)
    | .group source => some (source.referencesField field && query.atPath source.source.groupPath source.source.bindingScope (source.source.groupPath.length == 1))
    | .selected source => some (selectedReferenceAt field query source.source))

private def tokenReferenceAt? (field : FieldId) (query : ReferenceQuery)
    (source : CheckedTokenEntitySource model) : Option Bool :=
  anyReference (source.operands.map fun
    | .field source => some (source.declaration.id == field && query.binds source.declaration.repeatableScope)
    | .star source => some ((source.source.declaration.id == field && query.binds source.source.bindingScope) ||
        source.filter.any (fun filter => markedReferenceAt model field query filter.condition))
    | .group source => some (source.referencesField field && query.atPath source.source.groupPath source.source.bindingScope (source.source.groupPath.length == 1))
    | .selected source => some (selectedReferenceAt field query source.source))

private def booleanCountReferenceAt? (field : FieldId) (query : ReferenceQuery)
    (source : CheckedBooleanValueCountSource model) : Option Bool :=
  anyReference (source.operands.map fun
    | .field source => some (source.declaration.id == field && query.binds source.declaration.repeatableScope)
    | .selected source => some (selectedReferenceAt field query source.source)
    | .star source => some ((source.source.declaration.id == field && query.binds source.source.bindingScope) ||
        source.filter.any (fun filter => markedReferenceAt model field query filter.condition))
    | .group source => some (source.referencesField field && query.atPath source.source.groupPath source.source.bindingScope (source.source.groupPath.length == 1)))

private def fillReferenceAt? (field : FieldId) (query : ReferenceQuery)
    (source : CheckedFieldFillList model) : Option Bool :=
  anyReference (source.operands.map fun operand => match operand with
    | .field declaration => some (declaration.id == field && query.binds declaration.repeatableScope)
    | .star source => some ((source.source.declaration.id == field && query.binds source.source.bindingScope) ||
        source.filter.any (fun filter => markedReferenceAt model field query filter.condition))
    | .group source => some (operand.referencesField field && query.atPath source.source.groupPath source.source.bindingScope (source.source.groupPath.length == 1))
    | .indexed source => some (selectedReferenceAt field query (.inl source))
    | .keyed source => some (selectedReferenceAt field query (.inr source)))

/-- Recursive amounts retain authored slots separately from their temporal children. Use the
slot's binding scope, rather than the surrounding temporal operand's scope (spec/07 §1). -/
private def temporalNumericReferenceAt? (field : FieldId) (query : ReferenceQuery)
    (atom : HavingNumericAtomOf (ScalarTemporalExpression model)) : Option Bool :=
  anyReference ((atom.presenceSlotsWith (fun _ _ => [])).map fun slot =>
    if !query.acceptsSlot slot || !slot.references.any (fun reference => reference.field == field) then some false else
    match query.kind with
    | .membership => some true
    | .nonFormMembership => some (!isFormSlot slot)
    | .iteration level => (slot.bindingScope? model).map (·.contains level)
    | .nonIteration level => (slot.bindingScope? model).map (!·.contains level)
    | .nonWildcard level => (slot.bindingScope? model).map (·.contains level)
    | .unkeyed _ => some true
    | .selected _ _ => some false
    | .unselected => some true
    | .unstarred fieldScope => (slot.bindingScope? model).map (fun scope => fieldScope.all scope.contains))

private def temporalReferenceAt? (field : FieldId) (query : ReferenceQuery)
    (source : ScalarTemporalExpression model) : Option Bool :=
  anyReference (source.dependenciesWith
    (fun candidate => [some (candidate == field && query.binds (model.fieldRepeatableScope candidate))])
    (fun source => [shapeReferenceAt? field query source.shape (source.filters.filterMap id)])
    (fun source => [some (selectedReferenceAt field query (.inl source))])
    (numeric := fun atom => [temporalNumericReferenceAt? field query atom]))

private def typedOperandReferenceAt? (field : FieldId) (query : ReferenceQuery) :
    CheckedFirstFilledComparisonOperand model → Option Bool
  | .firstFilled source => fillReferenceAt? field query source.source
  | .field declaration _ => some (declaration.id == field && query.binds declaration.repeatableScope)
  | .indexed source _ => some (selectedReferenceAt field query (.inl source))
  | .boolean _ => some false
  | .temporal source => temporalReferenceAt? field query source.core

private def ordinaryNumericAtomReferenceAt? (model : FlatModel) (field : FieldId)
    (query : ReferenceQuery) (atom : NumericValidationAtom) : Option Bool :=
  if !atom.referencesField model field then some false else
  match atom with
  | .filledGroupCount groups => some (groups.any fun reference =>
      reference.referencesField model field && query.atPath reference.path reference.boundRepeatableScope reference.isRoot)
  | _ => some (query.binds (model.fieldRepeatableScope field))

private def numericAtomReferenceAt? (field : FieldId) (query : ReferenceQuery)
    (atom : OrderedNumericValidationAtom model) : Option Bool :=
  if !atom.referencesErrorField field then some false else
  match atom with
  | .firstFilled source | .valueCount _ source | .aggregate _ source => numberReferenceAt? field query source
  | .tokenValueCount source => tokenReferenceAt? field query source.source
  | .booleanValueCount source => booleanCountReferenceAt? field query source
  | .tokenDistinctCount source => tokenReferenceAt? field query source
  | .temporalDistinctCount run =>
      shapeReferenceAt? field query run.source.shape (run.source.operands.filterMap fun
        | .slot (.star _ _ filter) => filter
        | _ => none)
  | .filledFieldCount source => fillReferenceAt? field query source
  | .temporalExpression source =>
      match source.core with
      | .temporal operation =>
          anyReference (operation.sources.map fun source => temporalReferenceAt? field query source.core)
      | .storedProjection source =>
          anyReference (source.dependenciesWith
            (fun candidate => [some (candidate == field && query.binds (model.fieldRepeatableScope candidate))])
            (fun source => [shapeReferenceAt? field query source.shape (source.filters.filterMap id)])
            (fun source => [some (selectedReferenceAt field query (.inl source))])
            (numeric := fun atom => [temporalNumericReferenceAt? field query atom]))
  | .indexed source => some (selectedReferenceAt field query (.inl source.toCheckedSemanticIndexSource))
  | .indexedString source => some (selectedReferenceAt field query (.inl source.selection))
  | .sumOfProducts (.selected source) => some (
      selectedReferenceAt field query (.inr source.left.source) ||
      selectedReferenceAt field query (.inr source.right.source))
  | .sumOfProducts (.row source) => some (
      (source.left.field.id == field && query.binds source.left.source.bindingScope) ||
      (source.right.field.id == field && query.binds source.right.source.bindingScope))
  | .filledGroupCountMixed operands => some (operands.any fun operand =>
      operand.referencesField model field && query.atPath operand.groupPath operand.bindingScope operand.isRoot)
  | .ordinary source => ordinaryNumericAtomReferenceAt? model field query source

private def numericExpressionReferenceAt? (referenceAt : Atom → Option Bool)
    (expression : AuthoredNumericExpr Atom) : Option Bool :=
  if expression.anyAtom (fun atom => referenceAt atom == some true) then some true
  else if expression.anyAtom (fun atom => (referenceAt atom).isNone) then none
  else some false

private def tokenOperandReferenceAt? (field : FieldId) (query : ReferenceQuery) :
    CheckedTokenComparisonOperand model → Option Bool
  | .literal _ => some false
  | .field source => some (source.declaration.id == field && query.binds source.declaration.repeatableScope)
  | .firstFilled source _ => tokenReferenceAt? field query source

private def overlapReferenceAt? (field : FieldId) (query : ReferenceQuery)
    (condition : IteratedDateRangeCondition model) : Option Bool :=
  match condition with
  | .overlap source => shapeReferenceAt? field query source.shape condition.filters
  | .pluralOverlap source => shapeReferenceAt? field query source.shape condition.filters
  | .yearlessOverlap source | .yearlessPluralOverlap source =>
      shapeReferenceAt? field query source.shape condition.filters
  | _ => some ((condition.operandDeclarations.any fun declaration =>
      declaration.id == field && query.binds declaration.repeatableScope) ||
      condition.constructionEndpoints.any (fun endpoint => endpoint.selection?.any fun selection =>
        selectedReferenceAt field query (.inl selection.val)))

private def leafErrorReferenceAt? (field : FieldId) (query : ReferenceQuery)
    (leaf : ValidationConditionLeaf model) : Option Bool :=
  if !leaf.referencesErrorField field then some false else
  match leaf with
  | .customCondition _ => some false
  | .flat _ | .customFieldValidity _ | .stringPattern _ =>
      some (query.binds (model.fieldRepeatableScope field))
  | .indexedStringPattern source => some (selectedReferenceAt field query (.inl source.selection))
  | .indexedCustomFieldValidity source => some (selectedReferenceAt field query (.inl source.source.selection))
  | .stringExpression comparison =>
      anyReference ((comparison.left.core.fields ++ comparison.right.core.fields).map fun
        | .inl candidate => some (candidate == field && query.binds (model.fieldRepeatableScope candidate))
        | .inr source => some (selectedReferenceAt field query (.inl source)))
  | .valueList (.number source) => anyReference [
      numberReferenceAt? field query source.fields, numberReferenceAt? field query source.values]
  | .valueList (.token source) => anyReference [
      tokenReferenceAt? field query source.fields, tokenReferenceAt? field query source.values]
  | .valueList (.literals source) => tokenReferenceAt? field query source.fields
  | .indexedFieldPresence _ source => some (selectedReferenceAt field query (.inl source))
  | .keyedGroupPresence _ source => some (selectedReferenceAt field query (.inr source))
  | .repeatableFieldPresence _ declaration => some (query.binds declaration.repeatableScope)
  | .guardedRootCurrentRepetition _ _ _ => some (query.binds [])
  | .guardedRepeatableCurrentRepetition declaration _ _ => some (query.binds declaration.repeatableScope)
  | .groupPresence _ reference => some (query.atPath reference.path (model.repeatableScopeForGroupPath reference.path) reference.isRoot)
  | .groupList _ operands => anyReference (operands.map fun operand =>
      if !operand.referencesField field then some false else
      match operand with
      | .indexed source => some (selectedReferenceAt field query (.inl source))
      | .keyed source => some (selectedReferenceAt field query (.inr source))
      | .group reference => some (query.atPath reference.path reference.boundRepeatableScope reference.isRoot)
      | _ => some (query.acceptsPath operand.entityPath && match query.kind with
          | .membership => true
          | .nonFormMembership => !operand.isRootGroup
          | .iteration level => operand.iterationScope.any (·.contains level)
          | .nonIteration level => !operand.iterationScope.any (·.contains level)
          | .nonWildcard level => operand.iterationScope.any (·.contains level)
          | .unkeyed _ => true
          | .selected _ _ => false
          | .unselected => true
          | .unstarred fieldScope => operand.iterationScope.any (fun scope => fieldScope.all scope.contains)))
  | .fieldFill _ source => fillReferenceAt? field query source
  | .valuesNotUnique (.number source) => numberReferenceAt? field query source
  | .valuesNotUnique (.token source) => tokenReferenceAt? field query source.source
  | .valuesNotUnique (.temporal source) =>
      shapeReferenceAt? field query source.shape (source.operands.filterMap fun
        | .star _ _ filter => filter
        | _ => none)
  | .numeric _ comparison => anyReference [
      numericExpressionReferenceAt? (ordinaryNumericAtomReferenceAt? model field query) comparison.left,
      numericExpressionReferenceAt? (ordinaryNumericAtomReferenceAt? model field query) comparison.right]
  | .orderedNumeric _ comparison => anyReference [
      numericExpressionReferenceAt? (numericAtomReferenceAt? field query) comparison.left,
      numericExpressionReferenceAt? (numericAtomReferenceAt? field query) comparison.right]
  | .firstFilledComparison comparison => anyReference [
      typedOperandReferenceAt? field query comparison.left,
      typedOperandReferenceAt? field query comparison.right]
  | .tokenComparison comparison => anyReference [
      tokenOperandReferenceAt? field query comparison.left,
      tokenOperandReferenceAt? field query comparison.right]
  | .scalarTemporal comparison => anyReference [
      temporalReferenceAt? field query comparison.left.core,
      temporalReferenceAt? field query comparison.right.core]
  | .constructedDateValidity _ source => temporalReferenceAt? field query source.scalarCore
  | .iteratedDateRange condition => overlapReferenceAt? field query condition
  | .repetitionNotUnique source => some (
      (source.keys.any (fun key => key.fieldId == field) &&
        query.binds (model.fieldRepeatableScope field)) ||
      match source.referenceOrigin with
      | .inferredDefault => false
      | .authoredFrom =>
          let reference : ResolvedGroupReference := { path := source.referenceGroup.path, origin := .path }
          reference.referencesField model field &&
            query.atPath reference.path (model.repeatableScopeForGroupPath reference.path) reference.isRoot)

private def errorReferenceFor? (condition : ValidationCondition model)
    (field : FieldId) (query : ReferenceQuery) : Option Bool :=
  match condition with
  | .leaf leaf => leafErrorReferenceAt? field query leaf
  | .and left right | .or left right =>
      anyReference [errorReferenceFor? left field query, errorReferenceFor? right field query]

/-- Authored static references exclude implicit cache dependencies (spec/07 §1). -/
def authoredErrorReference? (condition : ValidationCondition model) (field : FieldId) : Option Bool :=
  errorReferenceFor? condition field { kind := .membership }

/-- Whether the error field is reached through its root group alone. An unresolved carrier
cannot certify this partition (spec/07 §1; `reachedThroughFormAlone`). -/
def formOnlyErrorReference? (condition : ValidationCondition model) (field : FieldId) : Option Bool := do
  let member ← errorReferenceFor? condition field { kind := .membership }
  let nonForm ← errorReferenceFor? condition field { kind := .nonFormMembership }
  pure (member && !nonForm)

/-- Whether any reference naming the error field binds the queried ordinary iteration level.
`none` preserves an unresolved reference carrier; it is not a positive correspondence claim. -/
def errorReferenceAt? (condition : ValidationCondition model)
    (field : FieldId) (level : RepeatableLevel) : Option Bool :=
  if !(model.fieldRepeatableScope field).contains level then some false
  else errorReferenceFor? condition field { kind := .iteration level }

/-- Unlike error-field membership, an index reference must descend from an authored entity
inside the indexed group; a read of its parent does not name all descendant indices. -/
def messageGroupReference? (condition : ValidationCondition model)
    (field : FieldId) (group : GroupPath) : Option Bool :=
  errorReferenceFor? condition field { kind := .membership, within := some group }

/-- Message parameters inspect each authored reference mode, including a non-iterating read beside
an iterating read of the same field (spec/11; checkIndexFieldRefRepeatability4repeatableGroup). -/
def messageNonIteratingReference? (condition : ValidationCondition model)
    (field : FieldId) (group : GroupPath) (level : RepeatableLevel) : Option Bool :=
  errorReferenceFor? condition field { kind := .nonIteration level, within := some group }

def messageNonWildcardReference? (condition : ValidationCondition model)
    (field : FieldId) (group : GroupPath) (level : RepeatableLevel) : Option Bool :=
  errorReferenceFor? condition field { kind := .nonWildcard level, within := some group }

/-- The keyed-group parameter and index terminal share this condition-owned selection inventory.
Literal spelling is irrelevant after the checked key has established its typed identity. -/
def messageSelectedGroupReference? (condition : ValidationCondition model)
    (field : FieldId) (group : GroupPath) (key : Option CheckedSemanticIndexKey) : Option Bool :=
  errorReferenceFor? condition field { kind := .selected group key, within := some group }

def messageUnkeyedReference? (condition : ValidationCondition model)
    (field : FieldId) (group : GroupPath) (level : RepeatableLevel) : Option Bool :=
  errorReferenceFor? condition field { kind := .unkeyed level, within := some group }

/-- Whether the condition reads `field` other than through a semantic-index selection of it. An
unkeyed message parameter is a member only through such a read: a keyed read of the same field does
not license it ([checkpoint](../../../docs/sources/message-and-pointer-probes.md#src-rule-message-semantic-index),
`membership-claim`). -/
def messageUnselectedReference? (condition : ValidationCondition model) (field : FieldId) :
    Option Bool :=
  errorReferenceFor? condition field { kind := .unselected }

/-- Whether some read of `field` binds every one of its repeatable levels, so that no wildcard was
written on its path. The value suffix needs one; a read only through a star does not supply it, while
a plain group read containing the field does
([parameter surface](../../../docs/sources/message-and-pointer-probes.md#src-message-parameter-surface-and-iteration-gates),
[group footprint](../../../docs/sources/inbound-handbacks.md#inbound-2026-09-30a-message-reference-admission)). -/
def messageUnstarredReference? (condition : ValidationCondition model) (field : FieldId) :
    Option Bool :=
  errorReferenceFor? condition field { kind := .unstarred (model.fieldRepeatableScope field) }

end A12Kernel.ValidationCondition
