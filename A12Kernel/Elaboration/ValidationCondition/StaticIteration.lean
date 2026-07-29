import A12Kernel.Elaboration.ValidationCondition.Core

/-! # Validation-condition static iteration scope

This module derives ordinary repeatable scope from checked condition sources. The
level-local legality classifier and addressed execution consume this model-owned scope
without adding another topology or reference walk.
-/

namespace A12Kernel

namespace ValidationCondition

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

def ResolvedGroupListOperands.iterationScope
    (operands : List (ResolvedGroupListOperand model)) :
    Except RuleIterationScopeError (Option (List RepeatableLevel)) :=
  mergeIterationScopeList
    (operands.map ResolvedGroupListOperand.iterationScope)

private def repeatableScopeThrough :
    List RepeatableLevel → RepeatableLevel →
      Option (List RepeatableLevel)
  | [], _ => none
  | level :: remaining, target =>
      if level == target then
        some [level]
      else
        (repeatableScopeThrough remaining target).map (level :: ·)

private def outerHavingNumberIterationScope
    (model : FlatModel) (reference : HavingNumberRef) :
    Option (List RepeatableLevel) :=
  match reference.origin with
  | .inner => none
  | .outer =>
      match model.lookupUniqueId reference.field.id with
      | .error _ => none
      | .ok declaration =>
          if declaration.repeatableScope.isEmpty then
            none
          else
            some declaration.repeatableScope

private def outerHavingRepetitionIterationScope
    (outerLevels : List RepeatableLevel)
    (reference : HavingRepetitionRef) :
    Option (List RepeatableLevel) :=
  match reference.origin with
  | .inner => none
  | .outer => repeatableScopeThrough outerLevels reference.level

private def correlatedHavingOuterIterationScopes
    (model : FlatModel) (outerLevels : List RepeatableLevel) :
    CorrelatedHaving → List (Option (List RepeatableLevel))
  | .leaf (.compareNumbers _ left right) =>
      [outerHavingNumberIterationScope model left,
        outerHavingNumberIterationScope model right]
  | .leaf (.compareRepetitions _ left right) =>
      [outerHavingRepetitionIterationScope outerLevels left,
        outerHavingRepetitionIterationScope outerLevels right]
  | .and left right | .or left right =>
      correlatedHavingOuterIterationScopes model outerLevels left ++
        correlatedHavingOuterIterationScopes model outerLevels right

private def checkedHavingOuterIterationScope
    (checked : CheckedStarHaving model source declaringGroup) :
    Except RuleIterationScopeError (Option (List RepeatableLevel)) :=
  mergeIterationScopeList
    (correlatedHavingOuterIterationScopes model
      (model.repeatableScopeForGroupPath declaringGroup)
      checked.condition)

private def checkedNumberOperandIterationScope :
    CheckedNumberEntityOperand model →
      Except RuleIterationScopeError (Option (List RepeatableLevel))
  | .field _ => pure none
  | .star source => pure (checkedStarBindingScope source.source)
  | .starHaving source => do
      mergeIterationScopes
        (checkedStarBindingScope source.source.source)
        (← checkedHavingOuterIterationScope source.filter)

private def checkedTokenOperandIterationScope :
    CheckedTokenEntityOperand model →
      Except RuleIterationScopeError (Option (List RepeatableLevel))
  | .field _ => pure none
  | .star source =>
      match source.filter with
      | none => pure (checkedStarBindingScope source.source)
      | some filter => do
          mergeIterationScopes
            (checkedStarBindingScope source.source)
            (← checkedHavingOuterIterationScope filter)

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
  | .star source =>
      match source.filter with
      | none => pure (checkedStarBindingScope source.source)
      | some filter => do
          mergeIterationScopes
            (checkedStarBindingScope source.source)
            (← checkedHavingOuterIterationScope filter)

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
  | .baseYear year _ =>
      if model.baseYear == some year then some [] else none

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
        (fun source => source.kind == .date &&
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
                source.kind == .dateTime &&
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
          CalendarDayDifference.admittedBy source.kind source.components)
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
  | .ordinary source => ordinaryNumericAtomIterationScope model source
  | .firstFilled source | .valueCount _ source | .aggregate _ source =>
      checkedNumberSourceIterationScope source
  | .tokenValueCount source =>
      checkedTokenSourceIterationScope source.source
  | .booleanValueCount source =>
      checkedBooleanValueCountSourceIterationScope source
  | .sumOfProducts source =>
      mergeIterationScopes
        (checkedStarBindingScope source.left.source)
        (checkedStarBindingScope source.right.source)

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
  | .leaf (.repeatableFieldPresence _ declaration) =>
      pure (some declaration.repeatableScope)
  | .leaf (.groupPresence _ reference) =>
      let scope := model.repeatableScopeForGroupPath reference.path
      pure (if scope.isEmpty then none else some scope)
  | .leaf (.orderedNumeric _ comparison) =>
      orderedNumericComparisonIterationScope comparison
  | .leaf (.groupList _ operands) =>
      ResolvedGroupListOperands.iterationScope operands
  | .leaf (.repetitionNotUnique source) =>
      pure (some (source.topology.path.axes.map (·.level)))
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
