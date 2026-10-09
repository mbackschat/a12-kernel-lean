import A12Kernel.Elaboration.ValidationCondition.Evaluation

/-! # Validation-condition static iteration scope

This module derives ordinary repeatable scope from checked condition sources. The
level-local legality classifier and addressed execution consume this model-owned scope
without adding another topology or reference walk.
-/

namespace A12Kernel

namespace ValidationCondition

inductive RuleIterationScopeError where
  | incompatibleScopes (left right : List RepeatableLevel)
  deriving Repr, DecidableEq

private def mergeIterationScopes
    (left right : Option (List RepeatableLevel)) :
    Except RuleIterationScopeError (Option (List RepeatableLevel)) :=
  match left, right with
  | none, scope | scope, none => pure scope
  | some leftScope, some rightScope =>
      if repeatableScopeAvailable leftScope rightScope then
        pure (some rightScope)
      else if repeatableScopeAvailable rightScope leftScope then
        pure (some leftScope)
      else
        throw (.incompatibleScopes leftScope rightScope)

def checkedStarBindingScope
    (source : CheckedStarFieldPath model) :
    Option (List RepeatableLevel) :=
  let scope := source.bindingScope
  if scope.isEmpty then none else some scope

private def mergeIterationScopeList :
    List (Option (List RepeatableLevel)) →
      Except RuleIterationScopeError (Option (List RepeatableLevel))
  | [] => pure none
  | scope :: remaining => do
      mergeIterationScopes scope (← mergeIterationScopeList remaining)

private def selectedIterationScope
    (source : Sum (CheckedSemanticIndexSource model) (CheckedKeyedEntityExtent model)) :
    Except RuleIterationScopeError (Option (List RepeatableLevel)) :=
  let scopes := match source with | .inl selected => selected.bindingScopes | .inr selected => selected.bindingScopes
  mergeIterationScopeList (scopes.map fun scope => if scope.isEmpty then none else some scope)

def ResolvedGroupListOperands.iterationScope
    (operands : List (ResolvedGroupListOperand model)) :
    Except RuleIterationScopeError (Option (List RepeatableLevel)) :=
  do mergeIterationScopeList (← operands.mapM fun
    | .indexed source => selectedIterationScope (.inl source)
    | .keyed source => selectedIterationScope (.inr source)
    | operand => pure operand.iterationScope)

private def checkedHavingOuterIterationScope
    (checked : CheckedStarHaving model source declaringGroup) :
    Except RuleIterationScopeError (Option (List RepeatableLevel)) :=
  mergeIterationScopeList
    (CorrelatedHaving.outerIterationScopes model checked.condition)

private def checkedNumberOperandIterationScope :
    CheckedNumberEntityOperand model →
      Except RuleIterationScopeError (Option (List RepeatableLevel))
  | .selected source => selectedIterationScope source.source
  | .field source =>
      pure (if source.declaration.repeatableScope.isEmpty then none
        else some source.declaration.repeatableScope)
  | .star source => pure (checkedStarBindingScope source.source)
  | .starHaving source => do
      mergeIterationScopes
        (checkedStarBindingScope source.source.source)
        (← checkedHavingOuterIterationScope source.filter)
  | .group slot =>
      -- A fixed group sits outside every repeatable scope and binds nothing; a starred group
      -- binds exactly the levels above its own star, on the same rule a starred field follows.
      let scope := slot.source.bindingScope
      pure (if scope.isEmpty then none else some scope)

private def checkedTokenOperandIterationScope :
    CheckedTokenEntityOperand model →
      Except RuleIterationScopeError (Option (List RepeatableLevel))
  | .field _ => pure none
  | .selected source => selectedIterationScope source.source
  | .star source =>
      match source.filter with
      | none => pure (checkedStarBindingScope source.source)
      | some filter => do
          mergeIterationScopes
            (checkedStarBindingScope source.source)
            (← checkedHavingOuterIterationScope filter)
  | .group slot =>
      -- Same rule as the Number carrier's group slot above, and for the same reason: the scope is
      -- read off the authored reference, not off the expansion.
      let scope := slot.source.bindingScope
      pure (if scope.isEmpty then none else some scope)

private def checkedNumberSourceIterationScope
    (source : CheckedNumberEntitySource model) :
    Except RuleIterationScopeError (Option (List RepeatableLevel)) := do
  mergeIterationScopeList
    (← source.operands.mapM checkedNumberOperandIterationScope)

private def checkedTokenSourceIterationScope
    (source : CheckedTokenEntitySource model) :
    Except RuleIterationScopeError (Option (List RepeatableLevel)) := do
  mergeIterationScopeList
    (← source.operands.mapM checkedTokenOperandIterationScope)

private def checkedBooleanValueCountOperandIterationScope :
    CheckedBooleanValueCountOperand model expected →
      Except RuleIterationScopeError (Option (List RepeatableLevel))
  | .field _ => pure none
  | .selected source => selectedIterationScope source.source
  | .star source =>
      match source.filter with
      | none => pure (checkedStarBindingScope source.source)
      | some filter => do
          mergeIterationScopes
            (checkedStarBindingScope source.source)
            (← checkedHavingOuterIterationScope filter)
  | .group slot =>
      let scope := slot.source.bindingScope
      pure (if scope.isEmpty then none else some scope)

private def checkedBooleanValueCountSourceIterationScope
    (source : CheckedBooleanValueCountSource model) :
    Except RuleIterationScopeError (Option (List RepeatableLevel)) := do
  mergeIterationScopeList
    (← source.operands.mapM
      checkedBooleanValueCountOperandIterationScope)

private def temporalDifferenceOperandDeclarations?
    (model : FlatModel) (accepts : FlatTemporalField → Bool) :
    ResolvedDateDifferenceOperand → Option (List FlatFieldDecl)
  | .field source =>
      match model.lookupUniqueId source.id with
      | .ok declaration =>
          if declaration.toTemporalField? == some source && accepts source then
            some [declaration]
          else none
      | .error _ => none
  | .literal source year =>
      if source.admittedIn model year then some [] else none
  | .baseYear year _ =>
      if model.baseYear == some year then some [] else none
  | .today profile =>
      if ModelZone.ConcreteProfile.ofId? model.timeZoneId == some profile then some [] else none

def ordinaryNumericAtomFieldDeclarations?
    (model : FlatModel) :
    NumericValidationAtom → Option (List FlatFieldDecl)
  | .field source =>
      match model.lookupUniqueId source.id with
      | .ok declaration =>
          if declaration.toNumberField? == some source then
            some [declaration]
          else none
      | .error _ => none
  | .temporalFieldPart source part =>
      match model.lookupUniqueId source.id with
      | .ok declaration =>
          if declaration.toTemporalField? == some source &&
              part.admittedBy source model.hasBaseYear then
            some [declaration]
          else none
      | .error _ => none
  | .dateRangeBoundPart source _ part =>
      -- The exposure predicate already certifies the DateRange input profile, so a non-DateRange
      -- declaration cannot reach the iteration scope through this atom.
      match model.lookupUniqueId source.id with
      | .ok declaration =>
          if model.exposesDateRangeBoundPart source part then
            some [declaration]
          else none
      | .error _ => none
  | .stringLength source =>
      match model.lookupUniqueId source.id with
      | .ok declaration =>
          if declaration.toStringValueField? == some source then
            some [declaration]
          else none
      | .error _ => none
  | .stringRange source _ _ =>
      match model.lookupUniqueId source.id with
      | .ok declaration =>
          if declaration.toStringValueField? == some source then
            some [declaration]
          else none
      | .error _ => none
  | .fieldValueAsNumber source =>
      (model.certifiedFieldValueAsNumberDeclaration? source).map (· :: [])
  | .dateDifference unit left right => do
      let declarations := temporalDifferenceOperandDeclarations? model
        (fun source =>
          unit.admittedBy model.hasBaseYear source.components)
      let leftDeclarations ← declarations left
      let rightDeclarations ← declarations right
      if unit.compatible model.hasBaseYear left.components right.components then
        some (leftDeclarations ++ rightDeclarations)
      else none
  | .dateTimeDifference unit left right => do
      let declarationsFor : FlatTemporalOperand → Option (List FlatFieldDecl)
        | .fieldValue source => do
            let declaration ← model.lookupUniqueId source.id |>.toOption
            if declaration.toTemporalField? == some source &&
                unit.admittedBy source.components then
              some [declaration]
            else
              none
        | .nowValue => some []
        | _ => none
      let leftDeclarations ← declarationsFor left
      let rightDeclarations ← declarationsFor right
      let leftComponents ← left.dateTimeDifferenceComponents?
      let rightComponents ← right.dateTimeDifferenceComponents?
      if unit.compatible leftComponents rightComponents then
        some (leftDeclarations ++ rightDeclarations)
      else none
  | .dayDifference profile left right => do
      if ModelZone.ConcreteProfile.ofId? model.timeZoneId != some profile then
        none
      let declarations := temporalDifferenceOperandDeclarations? model
        (fun source =>
          CalendarDayDifference.admittedBy source.components)
      let leftDeclarations ← declarations left
      let rightDeclarations ← declarations right
      if CalendarDayDifference.yearCompatible model.hasBaseYear
          left.components right.components then
        some (leftDeclarations ++ rightDeclarations)
      else none
  | _ => none

private def ordinaryNumericAtomIterationScope
    (model : FlatModel) (source : NumericValidationAtom) :
    Except RuleIterationScopeError (Option (List RepeatableLevel)) :=
  match source with
  | .boundCurrentRepetition repetition => pure (some repetition.scope)
  | .filledGroupCount groups =>
      mergeIterationScopeList (groups.map fun reference =>
        if reference.boundRepeatableScope.isEmpty then
          none
        else
          some reference.boundRepeatableScope)
  | _ =>
      match ordinaryNumericAtomFieldDeclarations? model source with
      | none => pure none
      | some declarations =>
          mergeIterationScopeList (declarations.map fun declaration =>
            if declaration.repeatableScope.isEmpty then
              none
            else
              some declaration.repeatableScope)

private def orderedNumericAtomIterationScope :
    OrderedNumericValidationAtom model →
      Except RuleIterationScopeError (Option (List RepeatableLevel))
  | .indexed source => selectedIterationScope (.inl source.toCheckedSemanticIndexSource)
  | .indexedString source =>
      mergeIterationScopeList (source.selection.bindingScopes.map fun scope => if scope.isEmpty then none else some scope)
  | .temporalExpression source =>
      mergeIterationScopeList (source.bindingScopes.map fun scope => if scope.isEmpty then none else some scope)
  | .ordinary source => ordinaryNumericAtomIterationScope model source
  | .firstFilled source | .valueCount _ source | .aggregate _ source =>
      checkedNumberSourceIterationScope source
  | .tokenValueCount source =>
      checkedTokenSourceIterationScope source.source
  | .tokenDistinctCount source => checkedTokenSourceIterationScope source
  | .temporalDistinctCount run => do
      let groupScope (source : CheckedEntityGroupSource model) :=
        let scope := source.bindingScope
        if scope.isEmpty then none else some scope
      mergeIterationScopeList (← run.source.operands.mapM fun operand =>
        match operand with
        | .slot (.field _) => pure none
        | .slot (.selected source _) | .selected source _ => selectedIterationScope source.source
        | .slot (.star path _ none) => pure (checkedStarBindingScope path)
        | .slot (.star path _ (some filter)) => do
            mergeIterationScopes (checkedStarBindingScope path)
              (← mergeIterationScopeList (CorrelatedHaving.outerIterationScopes model filter))
        | .slot (.group source) => pure (groupScope source.source)
        | .group source => pure (groupScope source.source))
  | .booleanValueCount source =>
      checkedBooleanValueCountSourceIterationScope source
  | .sumOfProducts (.selected source) => do
      mergeIterationScopes (← selectedIterationScope (.inr source.left.source))
        (← selectedIterationScope (.inr source.right.source))
  | .sumOfProducts (.row source) =>
      mergeIterationScopes
        (checkedStarBindingScope source.left.source)
        (checkedStarBindingScope source.right.source)
  -- A starred member reopens its own axis inside the count, but a level it leaves unstarred above
  -- its first star is read per row, on the rule every other star follows: bound from inside that
  -- level and refused from outside it
  -- ([checkpoint](../../../docs/sources/group-list-and-capacity-probes.md#src-computation-star-binding-gate)).
  | .filledFieldCount source =>
      let scope := source.bindingScope
      pure (if scope.isEmpty then none else some scope)
  | .filledGroupCountMixed operands =>
      mergeIterationScopeList (operands.map fun operand =>
        let scope := operand.bindingScope
        if scope.isEmpty then none else some scope)

private def authoredNumericIterationScope
    (scopeOf : Atom →
      Except RuleIterationScopeError (Option (List RepeatableLevel))) :
    AuthoredNumericExpr Atom →
      Except RuleIterationScopeError (Option (List RepeatableLevel))
  | .atom atom => scopeOf atom
  | .literal _ => pure none
  | .group body | .abs body | .extremumCall _ body | .round _ _ body =>
      authoredNumericIterationScope scopeOf body
  | .binary _ left right | .power left right | .extremum _ left right => do
      mergeIterationScopes
        (← authoredNumericIterationScope scopeOf left)
        (← authoredNumericIterationScope scopeOf right)

def orderedNumericComparisonIterationScope
    (comparison : OrderedNumericComparison model) :
    Except RuleIterationScopeError (Option (List RepeatableLevel)) := do
  mergeIterationScopes
    (← authoredNumericIterationScope
      orderedNumericAtomIterationScope comparison.left)
    (← authoredNumericIterationScope
      orderedNumericAtomIterationScope comparison.right)

/-- Derive one ordinary nonparallel rule-iteration scope from repeatable references. Ordinary references contribute their complete declaration scope; a star contributes only its nonempty binding prefix strictly above the first star. Nested compatible references select the deeper scope; sibling/cross-branch scopes remain explicit unsupported parallel work. -/
def ordinaryIterationScope :
    ValidationCondition model →
      Except RuleIterationScopeError (Option (List RepeatableLevel))
  | .leaf (.keyedGroupPresence _ source) =>
      mergeIterationScopeList (source.bindingScopes.map fun scope => if scope.isEmpty then none else some scope)
  | .leaf (.indexedFieldPresence _ source) =>
      mergeIterationScopeList (source.bindingScopes.map fun scope => if scope.isEmpty then none else some scope)
  | .leaf (.indexedStringPattern leaf) =>
      mergeIterationScopeList (leaf.bindingScopes.map fun scope => if scope.isEmpty then none else some scope)
  | .leaf (.indexedCustomFieldValidity leaf) =>
      mergeIterationScopeList (leaf.source.bindingScopes.map fun scope => if scope.isEmpty then none else some scope)
  | .leaf (.customFieldValidity leaf) =>
      let scope := leaf.operand.declaration.repeatableScope
      pure (if scope.isEmpty then none else some scope)
  | .leaf (.repeatableFieldPresence _ declaration) =>
      pure (some declaration.repeatableScope)
  | .leaf (.constructedDateValidity _ source) =>
      mergeIterationScopeList (source.scalarBindingScopes.map fun scope =>
        if scope.isEmpty then none else some scope)
  | .leaf (.stringPattern leaf) =>
      let scope := model.fieldRepeatableScope leaf.condition.field.id
      pure (if scope.isEmpty then none else some scope)
  | .leaf (.groupPresence _ reference) =>
      let scope := model.repeatableScopeForGroupPath reference.path
      pure (if scope.isEmpty then none else some scope)
  | .leaf (.orderedNumeric _ comparison) =>
      orderedNumericComparisonIterationScope comparison
  | .leaf (.groupList _ operands) =>
      ResolvedGroupListOperands.iterationScope operands
  | .leaf (.fieldFill _ source) =>
      mergeIterationScopeList (source.operands.flatMap fun operand =>
        operand.bindingScopes.map fun scope => if scope.isEmpty then none else some scope)
  | .leaf (.stringExpression comparison) =>
      mergeIterationScopeList (comparison.bindingScopes.map fun scope =>
        if scope.isEmpty then none else some scope)
  | .leaf (.scalarTemporal comparison) =>
      mergeIterationScopeList (comparison.bindingScopes.map fun scope =>
        if scope.isEmpty then none else some scope)
  | .leaf (.firstFilledComparison comparison) =>
      mergeIterationScopeList (comparison.bindingScopes.map fun scope =>
        if scope.isEmpty then none else some scope)
  | .leaf (.tokenComparison comparison) =>
      mergeIterationScopeList (comparison.bindingScopes.map fun scope =>
        if scope.isEmpty then none else some scope)
  | .leaf (.valueList source) =>
      source.bindingScopes.foldlM
        (fun scope next => mergeIterationScopes scope (if next.isEmpty then none else some next)) none
  | .leaf (.valuesNotUnique source) =>
      source.bindingScopes.foldlM
        (fun scope next => mergeIterationScopes scope (if next.isEmpty then none else some next)) none
  | .leaf (.repetitionNotUnique source) =>
      pure (some (source.topology.path.axes.map (·.level)))
  | .leaf (.guardedRepeatableCurrentRepetition guard _ _) =>
      pure (some guard.repeatableScope)
  | .leaf (.iteratedDateRange condition) =>
      mergeIterationScopeList (condition.bindingScopes.map fun scope =>
        if scope.isEmpty then none else some scope)
  | .leaf _ => pure none
  | .and left right | .or left right => do
      mergeIterationScopes
        (← ordinaryIterationScope left) (← ordinaryIterationScope right)

/-- Checked static legality for one condition across every derived ordinary repeatable level. `insufficient` preserves an operator family whose level-local guard rule is not yet classified instead of guessing legal or illegal. -/
inductive IterationLegality where
  | legal
  | invalid (level : RepeatableLevel)
  | insufficient (level : RepeatableLevel)
  deriving Repr, DecidableEq

/-- The kernel's direct Number/literal visitor treats exactly these ordinary operators as empty-zero negative conditions. Tolerance and the other ordinary directions remain admitted for this source shape. -/
def directEmptyZeroIsUnguarded :
    NumericValidationOp → Bool
  | .ordinary .equal | .ordinary .lessEqual
  | .ordinary .greaterEqual => true
  | _ => false

def directOrdinaryZeroSensitiveScope?
    (model : FlatModel) :
    AuthoredNumericExpr (OrderedNumericValidationAtom model) →
      Option (List RepeatableLevel)
  | .atom (.ordinary source) =>
      match ordinaryNumericAtomFieldDeclarations? model source with
      | none => none
      | some declarations =>
          match mergeIterationScopeList (declarations.map fun declaration =>
              if declaration.repeatableScope.isEmpty then
                none
              else
                some declaration.repeatableScope) with
          | .ok scope => scope
          | .error _ => none
  | _ => none

end ValidationCondition

end A12Kernel
