import A12Kernel.Elaboration.ValidationCondition.Core

/-! Error-field membership and error-field iteration are distinct static obligations (spec/07 §1).
A selected payload can name the error field without binding an ordinary iteration level. This
projection retains that distinction across the checked callers; unresolved carriers return `none`
rather than borrowing another operand's scope. -/

namespace A12Kernel.ValidationCondition

private def anyReference (answers : List (Option Bool)) : Option Bool :=
  if answers.contains (some true) then some true
  else if answers.contains none then none else some false

/-- Marking preserves the authored extent's scope; group membership does not bind its descendants
(IterationChecker.checkIteration4NotOnlyVRefs; spec/07 §1). -/
private def markedReferenceAt (model : FlatModel) (field : FieldId) (level : RepeatableLevel) :
    CorrelatedHaving → Bool
  | .and left right | .or left right =>
      markedReferenceAt model field level left || markedReferenceAt model field level right
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
          (slot.outerIterationScope? model).any (·.contains level)

private def rawOperandReferenceAt? (field : FieldId) (level : RepeatableLevel)
    (operand : ResolvedFieldEntityOperand model) : Option Bool :=
  match operand with
  | .indexed _ | .keyed _ => none
  | _ =>
      if !operand.expansionDeclarations.any (·.id == field) then some false
      else if operand.subtreePath?.any (fun path => path.length == 1) then none
      else some (operand.bindingScope.contains level)

private def shapeReferenceAt? (field : FieldId) (level : RepeatableLevel)
    (shape : CheckedFieldEntityShape model) (filters : List CorrelatedHaving := []) : Option Bool :=
  anyReference (some (filters.any (markedReferenceAt model field level)) ::
    shape.operands.map (rawOperandReferenceAt? field level))

private def numberReferenceAt? (field : FieldId) (level : RepeatableLevel)
    (source : CheckedNumberEntitySource model) : Option Bool :=
  anyReference (source.operands.map fun
    | .field source => some (source.field.id == field && source.declaration.repeatableScope.contains level)
    | .star source => some (source.field.id == field && source.source.bindingScope.contains level)
    | .starHaving source => some ((source.source.field.id == field && source.source.source.bindingScope.contains level) ||
        markedReferenceAt model field level source.having)
    | .group source => if source.source.groupPath.length == 1 then none else
        some (source.referencesField field && source.source.bindingScope.contains level)
    | .selected source => if source.referencesField field then none else some false)

private def tokenReferenceAt? (field : FieldId) (level : RepeatableLevel)
    (source : CheckedTokenEntitySource model) : Option Bool :=
  anyReference (source.operands.map fun
    | .field source => some (source.declaration.id == field && source.declaration.repeatableScope.contains level)
    | .star source => some ((source.source.declaration.id == field && source.source.bindingScope.contains level) ||
        source.filter.any (fun filter => markedReferenceAt model field level filter.condition))
    | .group source => if source.source.groupPath.length == 1 then none else
        some (source.referencesField field && source.source.bindingScope.contains level)
    | .selected source => if source.referencesField field then none else some false)

private def fillReferenceAt? (field : FieldId) (level : RepeatableLevel)
    (source : CheckedFieldFillList model) : Option Bool :=
  anyReference (source.operands.map fun operand => match operand with
    | .field declaration => some (declaration.id == field && declaration.repeatableScope.contains level)
    | .star source => some ((source.source.declaration.id == field && source.source.bindingScope.contains level) ||
        source.filter.any (fun filter => markedReferenceAt model field level filter.condition))
    | .group source => if source.source.groupPath.length == 1 then none else
        some (operand.referencesField field && source.source.bindingScope.contains level)
    | .indexed _ | .keyed _ => if operand.referencesField field then none else some false)

private def temporalReferenceAt? (field : FieldId) (level : RepeatableLevel)
    (source : ScalarTemporalExpression model) : Option Bool :=
  anyReference (source.dependenciesWith
    (fun candidate => [some (candidate == field && (model.fieldRepeatableScope candidate).contains level)])
    (fun source => [shapeReferenceAt? field level source.shape (source.filters.filterMap id)])
    (fun source => [if source.referencesField field then none else some false])
    (numeric := fun atom =>
      if (atom.fieldOriginsWith (fun _ => [])).any (fun reference => reference.2 == field)
      then [none] else [some false]))

private def numericAtomReferenceAt? (field : FieldId) (level : RepeatableLevel)
    (atom : OrderedNumericValidationAtom model) : Option Bool :=
  if !atom.referencesErrorField field then some false else
  match atom with
  | .firstFilled source | .valueCount _ source | .aggregate _ source => numberReferenceAt? field level source
  | .tokenValueCount source => tokenReferenceAt? field level source.source
  | .tokenDistinctCount source => tokenReferenceAt? field level source
  | .filledFieldCount source => fillReferenceAt? field level source
  | .temporalExpression source =>
      match source.core with
      | .temporal operation =>
          anyReference (operation.sources.map fun source => temporalReferenceAt? field level source.core)
      | .storedProjection source =>
          anyReference (source.dependenciesWith
            (fun candidate => [some (candidate == field && (model.fieldRepeatableScope candidate).contains level)])
            (fun source => [shapeReferenceAt? field level source.shape (source.filters.filterMap id)])
            (fun source => [if source.referencesField field then none else some false])
            (numeric := fun atom => (atom.fieldOriginsWith (fun _ => [])).map fun (_, candidate) =>
              some (candidate == field && (model.fieldRepeatableScope candidate).contains level)))
  | .ordinary (.field source) => some (source.id == field && (model.fieldRepeatableScope field).contains level)
  | _ => none

private def numericExpressionReferenceAt? (field : FieldId) (level : RepeatableLevel)
    (expression : AuthoredNumericExpr (OrderedNumericValidationAtom model)) : Option Bool :=
  if expression.anyAtom (fun atom => numericAtomReferenceAt? field level atom == some true) then some true
  else if expression.anyAtom (fun atom => (numericAtomReferenceAt? field level atom).isNone) then none
  else some false

private def tokenOperandReferenceAt? (field : FieldId) (level : RepeatableLevel) :
    CheckedTokenComparisonOperand model → Option Bool
  | .literal _ => some false
  | .field source => some (source.declaration.id == field && source.declaration.repeatableScope.contains level)
  | .firstFilled source _ => tokenReferenceAt? field level source

private def overlapReferenceAt? (field : FieldId) (level : RepeatableLevel)
    (condition : IteratedDateRangeCondition model) : Option Bool :=
  match condition with
  | .overlap source => shapeReferenceAt? field level source.shape condition.filters
  | .pluralOverlap source => shapeReferenceAt? field level source.shape condition.filters
  | .yearlessOverlap source | .yearlessPluralOverlap source =>
      shapeReferenceAt? field level source.shape condition.filters
  | _ => some (condition.operandDeclarations.any fun declaration =>
      declaration.id == field && declaration.repeatableScope.contains level)

private def leafErrorReferenceAt? (field : FieldId) (level : RepeatableLevel)
    (leaf : ValidationConditionLeaf model) : Option Bool :=
  if !leaf.referencesErrorField field then some false else
  match leaf with
  | .repeatableFieldPresence _ declaration => some (declaration.repeatableScope.contains level)
  | .guardedRootCurrentRepetition _ _ _ => some false
  | .guardedRepeatableCurrentRepetition declaration _ _ => some (declaration.repeatableScope.contains level)
  | .groupPresence _ reference => if reference.isRoot then none else
      some ((model.repeatableScopeForGroupPath reference.path).contains level)
  | .groupList _ operands => anyReference (operands.map fun operand =>
      if !operand.referencesField field then some false else
      match operand with
      | .indexed _ | .keyed _ => none
      | .group reference => if reference.isRoot then none else some (reference.boundRepeatableScope.contains level)
      | _ => some (operand.iterationScope.any (·.contains level)))
  | .fieldFill _ source => fillReferenceAt? field level source
  | .valuesNotUnique (.number source) => numberReferenceAt? field level source
  | .valuesNotUnique (.token source) => tokenReferenceAt? field level source.source
  | .valuesNotUnique (.temporal source) =>
      shapeReferenceAt? field level source.shape (source.operands.filterMap fun
        | .star _ _ filter => filter
        | _ => none)
  | .orderedNumeric _ comparison => anyReference [
      numericExpressionReferenceAt? field level comparison.left,
      numericExpressionReferenceAt? field level comparison.right]
  | .tokenComparison comparison => anyReference [
      tokenOperandReferenceAt? field level comparison.left,
      tokenOperandReferenceAt? field level comparison.right]
  | .scalarTemporal comparison => anyReference [
      temporalReferenceAt? field level comparison.left.core,
      temporalReferenceAt? field level comparison.right.core]
  | .constructedDateValidity _ source => temporalReferenceAt? field level source.scalarCore
  | .iteratedDateRange condition => overlapReferenceAt? field level condition
  | _ => none

/-- Whether any reference naming the error field binds the queried ordinary iteration level.
`none` preserves an unresolved reference carrier; it is not a positive correspondence claim. -/
def errorReferenceAt? (condition : ValidationCondition model)
    (field : FieldId) (level : RepeatableLevel) : Option Bool :=
  if !(model.fieldRepeatableScope field).contains level then some false else
  match condition with
  | .leaf leaf => leafErrorReferenceAt? field level leaf
  | .and left right | .or left right =>
      anyReference [errorReferenceAt? left field level, errorReferenceAt? right field level]

end A12Kernel.ValidationCondition
