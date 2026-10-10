import A12Kernel.Elaboration.ValidationCondition.Core

/-! Error-field membership and error-field iteration are distinct static obligations (spec/07 §1).
A selected payload can name the error field without binding an ordinary iteration level. This
projection retains that distinction across the checked callers; unresolved carriers return `none`
rather than borrowing another operand's scope. -/

namespace A12Kernel.ValidationCondition

private inductive ReferenceQuery where
  | membership
  | iteration (level : RepeatableLevel)

private def ReferenceQuery.binds (query : ReferenceQuery) (scope : List RepeatableLevel) : Bool :=
  match query with
  | .membership => true
  | .iteration level => scope.contains level

private def unresolvedReference (query : ReferenceQuery) (member : Bool) : Option Bool :=
  if !member then some false else
  match query with
  | .membership => some true
  | .iteration _ => none

/-- Static error references follow authored entities, not implicit index-cache reads
(EntityRefUtils.getDRefs/getGRefs; IterationChecker.checkIteration4NotOnlyVRefs).
Selection replaces its own iteration coordinate; a dynamic key keeps its independent scope. -/
private def selectedReferenceAt (field : FieldId) (query : ReferenceQuery)
    (source : Sum (CheckedSemanticIndexSource model) (CheckedKeyedEntityExtent model)) : Bool :=
  let selection := match source with | .inl source => source | .inr source => source.selection.indexSource
  let declarations := match source with | .inl source => [source.targetDeclaration] | .inr source => source.declarations
  let target := declarations.any (·.id == field) && query.binds selection.indexDeclaration.repeatableScope.dropLast
  let key := match selection.key with
    | .literal .. => false
    | .field declaration => declaration.id == field && query.binds declaration.repeatableScope
  target || key

private def anyReference (answers : List (Option Bool)) : Option Bool :=
  if answers.contains (some true) then some true
  else if answers.contains none then none else some false

/-- Marking preserves the authored extent's scope; group membership does not bind its descendants
(IterationChecker.checkIteration4NotOnlyVRefs; spec/07 §1). -/
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
      slots.any fun slot =>
        slot.references.any (fun reference => reference.origin == .outer && reference.field == field) &&
          match query with
          | .membership => true
          | .iteration level => (slot.outerIterationScope? model).any (·.contains level)

private def rawOperandReferenceAt? (field : FieldId) (query : ReferenceQuery)
    (operand : ResolvedFieldEntityOperand model) : Option Bool :=
  match operand with
  | .indexed source => some (selectedReferenceAt field query (.inl source))
  | .keyed source => some (selectedReferenceAt field query (.inr source))
  | _ =>
      if !operand.expansionDeclarations.any (·.id == field) then some false
      else if operand.subtreePath?.any (fun path => path.length == 1) then unresolvedReference query true
      else some (query.binds operand.bindingScope)

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
    | .group source => if source.source.groupPath.length == 1 then unresolvedReference query (source.referencesField field) else
        some (source.referencesField field && query.binds source.source.bindingScope)
    | .selected source => some (selectedReferenceAt field query source.source))

private def tokenReferenceAt? (field : FieldId) (query : ReferenceQuery)
    (source : CheckedTokenEntitySource model) : Option Bool :=
  anyReference (source.operands.map fun
    | .field source => some (source.declaration.id == field && query.binds source.declaration.repeatableScope)
    | .star source => some ((source.source.declaration.id == field && query.binds source.source.bindingScope) ||
        source.filter.any (fun filter => markedReferenceAt model field query filter.condition))
    | .group source => if source.source.groupPath.length == 1 then unresolvedReference query (source.referencesField field) else
        some (source.referencesField field && query.binds source.source.bindingScope)
    | .selected source => some (selectedReferenceAt field query source.source))

private def booleanCountReferenceAt? (field : FieldId) (query : ReferenceQuery)
    (source : CheckedBooleanValueCountSource model) : Option Bool :=
  anyReference (source.operands.map fun
    | .field source => some (source.declaration.id == field && query.binds source.declaration.repeatableScope)
    | .selected source => some (selectedReferenceAt field query source.source)
    | .star source => some ((source.source.declaration.id == field && query.binds source.source.bindingScope) ||
        source.filter.any (fun filter => markedReferenceAt model field query filter.condition))
    | .group source => if source.source.groupPath.length == 1 then unresolvedReference query (source.referencesField field) else
        some (source.referencesField field && query.binds source.source.bindingScope))

private def fillReferenceAt? (field : FieldId) (query : ReferenceQuery)
    (source : CheckedFieldFillList model) : Option Bool :=
  anyReference (source.operands.map fun operand => match operand with
    | .field declaration => some (declaration.id == field && query.binds declaration.repeatableScope)
    | .star source => some ((source.source.declaration.id == field && query.binds source.source.bindingScope) ||
        source.filter.any (fun filter => markedReferenceAt model field query filter.condition))
    | .group source => if source.source.groupPath.length == 1 then unresolvedReference query (operand.referencesField field) else
        some (operand.referencesField field && query.binds source.source.bindingScope)
    | .indexed source => some (selectedReferenceAt field query (.inl source))
    | .keyed source => some (selectedReferenceAt field query (.inr source)))

private def temporalReferenceAt? (field : FieldId) (query : ReferenceQuery)
    (source : ScalarTemporalExpression model) : Option Bool :=
  anyReference (source.dependenciesWith
    (fun candidate => [some (candidate == field && query.binds (model.fieldRepeatableScope candidate))])
    (fun source => [shapeReferenceAt? field query source.shape (source.filters.filterMap id)])
    (fun source => [some (selectedReferenceAt field query (.inl source))])
    (numeric := fun atom =>
      if (atom.fieldOriginsWith (fun _ => [])).any (fun reference => reference.2 == field)
      then [unresolvedReference query true] else [some false]))

private def typedOperandReferenceAt? (field : FieldId) (query : ReferenceQuery) :
    CheckedFirstFilledComparisonOperand model → Option Bool
  | .firstFilled source => fillReferenceAt? field query source.source
  | .field declaration _ => some (declaration.id == field && query.binds declaration.repeatableScope)
  | .indexed source _ => some (selectedReferenceAt field query (.inl source))
  | .boolean _ => some false
  | .temporal source => temporalReferenceAt? field query source.core

private def numericAtomReferenceAt? (field : FieldId) (query : ReferenceQuery)
    (atom : OrderedNumericValidationAtom model) : Option Bool :=
  if !atom.referencesErrorField field then some false else
  match atom with
  | .firstFilled source | .valueCount _ source | .aggregate _ source => numberReferenceAt? field query source
  | .tokenValueCount source => tokenReferenceAt? field query source.source
  | .booleanValueCount source => booleanCountReferenceAt? field query source
  | .tokenDistinctCount source => tokenReferenceAt? field query source
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
            (numeric := fun atom => (atom.fieldOriginsWith (fun _ => [])).map fun (_, candidate) =>
              some (candidate == field && query.binds (model.fieldRepeatableScope candidate))))
  | .indexed source => some (selectedReferenceAt field query (.inl source.toCheckedSemanticIndexSource))
  | .indexedString source => some (selectedReferenceAt field query (.inl source.selection))
  | .ordinary (.field source) => some (source.id == field && query.binds (model.fieldRepeatableScope field))
  | _ => unresolvedReference query true

private def numericExpressionReferenceAt? (field : FieldId) (query : ReferenceQuery)
    (expression : AuthoredNumericExpr (OrderedNumericValidationAtom model)) : Option Bool :=
  if expression.anyAtom (fun atom => numericAtomReferenceAt? field query atom == some true) then some true
  else if expression.anyAtom (fun atom => (numericAtomReferenceAt? field query atom).isNone) then none
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
  | _ => some (condition.operandDeclarations.any fun declaration =>
      declaration.id == field && query.binds declaration.repeatableScope)

private def leafErrorReferenceAt? (field : FieldId) (query : ReferenceQuery)
    (leaf : ValidationConditionLeaf model) : Option Bool :=
  if !leaf.referencesErrorField field then some false else
  match leaf with
  | .indexedFieldPresence _ source => some (selectedReferenceAt field query (.inl source))
  | .keyedGroupPresence _ source => some (selectedReferenceAt field query (.inr source))
  | .repeatableFieldPresence _ declaration => some (query.binds declaration.repeatableScope)
  | .guardedRootCurrentRepetition _ _ _ => some (query.binds [])
  | .guardedRepeatableCurrentRepetition declaration _ _ => some (query.binds declaration.repeatableScope)
  | .groupPresence _ reference => if reference.isRoot then unresolvedReference query true else
      some (query.binds (model.repeatableScopeForGroupPath reference.path))
  | .groupList _ operands => anyReference (operands.map fun operand =>
      if !operand.referencesField field then some false else
      match operand with
      | .indexed source => some (selectedReferenceAt field query (.inl source))
      | .keyed source => some (selectedReferenceAt field query (.inr source))
      | .group reference => if reference.isRoot then unresolvedReference query true else some (query.binds reference.boundRepeatableScope)
      | _ => some (match query with
          | .membership => true
          | .iteration level => operand.iterationScope.any (·.contains level)))
  | .fieldFill _ source => fillReferenceAt? field query source
  | .valuesNotUnique (.number source) => numberReferenceAt? field query source
  | .valuesNotUnique (.token source) => tokenReferenceAt? field query source.source
  | .valuesNotUnique (.temporal source) =>
      shapeReferenceAt? field query source.shape (source.operands.filterMap fun
        | .star _ _ filter => filter
        | _ => none)
  | .orderedNumeric _ comparison => anyReference [
      numericExpressionReferenceAt? field query comparison.left,
      numericExpressionReferenceAt? field query comparison.right]
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
  | _ => unresolvedReference query true

private def errorReferenceFor? (condition : ValidationCondition model)
    (field : FieldId) (query : ReferenceQuery) : Option Bool :=
  match condition with
  | .leaf leaf => leafErrorReferenceAt? field query leaf
  | .and left right | .or left right =>
      anyReference [errorReferenceFor? left field query, errorReferenceFor? right field query]

/-- Authored static references exclude implicit cache dependencies; unresolved carriers preserve
legacy membership until their source-specific projection is known. -/
def authoredErrorReference? (condition : ValidationCondition model) (field : FieldId) : Option Bool :=
  errorReferenceFor? condition field .membership

/-- Whether any reference naming the error field binds the queried ordinary iteration level.
`none` preserves an unresolved reference carrier; it is not a positive correspondence claim. -/
def errorReferenceAt? (condition : ValidationCondition model)
    (field : FieldId) (level : RepeatableLevel) : Option Bool :=
  if !(model.fieldRepeatableScope field).contains level then some false
  else errorReferenceFor? condition field (.iteration level)

end A12Kernel.ValidationCondition
