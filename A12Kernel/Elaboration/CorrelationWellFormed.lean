import A12Kernel.Elaboration.HavingStringExpression
import A12Kernel.Elaboration.HavingNumericAtom
import A12Kernel.Elaboration.HavingSelectedComparison
import A12Kernel.Elaboration.HavingGroupCount
import A12Kernel.Elaboration.HavingNumericProduct
import A12Kernel.Elaboration.HavingCollectionCount
import A12Kernel.Elaboration.HavingNumberAggregate
import A12Kernel.Elaboration.HavingTemporalExpression
import A12Kernel.Elaboration.HavingDateValidity
import A12Kernel.Elaboration.HavingDateRange
import A12Kernel.Elaboration.HavingUniqueness
import A12Kernel.Elaboration.CheckedGroupPresence
import A12Kernel.Elaboration.Flat.FieldValueRead
import A12Kernel.Elaboration.SingleGroup
import A12Kernel.Elaboration.NumericSource
import A12Kernel.Elaboration.DateRangeBoundComponent
import A12Kernel.Semantics.Correlation
import A12Kernel.Elaboration.ComparisonEntry

/-! # Static well-formedness of a resolved filter tree

The predicates a checked filter certifies once its references are resolved: the operator-specific scale law, the legacy one-group route's admitted leaves, availability of every reference in the candidate and captured environments, and the requirement that an unmarked reference reach a reopened level. [`Correlation`](Correlation.lean) elaborates the authored filter into this tree and stores these predicates as its certificate.
-/

namespace A12Kernel

def CorrelationComparisonOp.acceptsScales (op : CorrelationComparisonOp)
    (left right : FlatNumberField) : Bool :=
  match op with
  | .equal | .notEqual => left.info.scale == right.info.scale
  | .lessThan | .lessEqual | .greaterThan | .greaterEqual => true

/-- The ordinary comparison's literal scale gate: `==` and `!=` accept a literal only when the field's
    declared scale can hold its authored fraction digits, while ordering is exempt, as measured on
    the filter leaf ([checkpoint](../../docs/sources/having-filter-probes.md#src-having-number-leaf-grid)). -/
def CorrelationComparisonOp.acceptsLiteralScale (op : CorrelationComparisonOp)
    (field : FlatNumberField) (literal : DecodedNumericLiteral) : Bool :=
  op.toNumeric.acceptsScales (.field field.info.scale) (.constant literal.authoredScale)


/-- Filter comparisons share numeric admission, the enclosing text's scale-warning suppression included. -/
def NumericComparisonOf.havingAdmitted (comparison : NumericComparisonOf HavingNumericAtom)
    (admitted : HavingNumericAtom → Bool) : Bool :=
  comparison.admittedWith admitted HavingNumericAtom.summary

/-- Operator-specific static scale law for one filter leaf: `==` and `!=` are gated; ordering and tolerance are exempt (spec/04 §4). -/
def CorrelatedHavingLeaf.equalityScalesAgree : CorrelatedHavingLeaf → Bool
  | .numeric comparison =>
      match comparison.left.summary? HavingNumericAtom.summary,
          comparison.right.summary? HavingNumericAtom.summary with
      | some left, some right => comparison.op.acceptsScalesWithSuppression
          comparison.suppressExactScaleWarning left right
      | _, _ => false
  -- Text, Boolean/Confirm and presence carry no declared scale; their kind gates belong to
  -- wellFormedForEnvironments.
  | .stringExpression _ | .selectedComparison _ | .temporalExpression _ | .simpleComparison _ _ _ | .compareStringLiteral _ _ _ | .fieldFill _ _ | .literalMembership _ _ _ | .fieldMembership _ _ | .dateValidity _ _ | .dateRange _ | .uniqueness _ | .presence _ _ | .typeValidity _ _ _ | .stringPattern _ _ _ | .groupPresence _ _ _ | .groupFill _ _ _ => true

/-- Every leaf under the shared connective tree satisfies the static scale law. -/
def CorrelatedHaving.equalityScalesAgree (condition : CorrelatedHaving) : Bool :=
  condition.allLeaves CorrelatedHavingLeaf.equalityScalesAgree

def CorrelatedHavingLeaf.wellFormedForSingleGroup
    (model : FlatModel) (group : RepeatableGroupDecl) : CorrelatedHavingLeaf → Bool
  | .numeric comparison => comparison.havingAdmitted fun
      | .baseYear year | .baseYearDatePart year _ _ => model.baseYear == some year
      | .firstFilled _ | .groupCount _ | .product _ | .collectionCount _ | .aggregate _ _ | .dateDifference _ _ _ | .dayDifference _ _ _ | .dateTimeDifference _ _ _ | .clockPart _ _ _ | .fieldValueAsNumber _ _ => false
      | .field reference => model.admitsSingleGroupNumber group reference.field
      | .dateRangeBoundPart _ _ _ _ | .stringLength _ _ | .stringRange _ _ _ _ | .temporalPart _ _ _ _ | .temporalExpressionPart _ _ | .temporalDifference _ _ _ => false
      | .repetition reference => reference.source == .repeatable group.level
  -- The legacy one-group adapter admits only the leaves it was built for. The other
  -- leaves reach the checked-star route instead, so refusing them here fails closed rather than
  -- extending an adapter no current consumer needs them on.
  | .stringExpression _ | .selectedComparison _ | .temporalExpression _ | .simpleComparison _ _ _ | .compareStringLiteral _ _ _ | .fieldFill _ _ | .literalMembership _ _ _ | .fieldMembership _ _ | .dateValidity _ _ | .dateRange _ | .uniqueness _ | .presence _ _ | .typeValidity _ _ _ | .stringPattern _ _ _ | .groupPresence _ _ _ | .groupFill _ _ _ => false

def CorrelatedHaving.wellFormedForSingleGroup (condition : CorrelatedHaving)
    (model : FlatModel) (group : RepeatableGroupDecl) : Bool :=
  condition.allLeaves fun leaf => leaf.wellFormedForSingleGroup model group

/-- Recheck the model-owned text projection and literal domain so a forged filter cannot bypass
    the same admission used by ordinary comparisons. -/
private def FlatModel.admitsHavingStringInEnvironment (model : FlatModel)
    (candidateLevels outerLevels : List RepeatableLevel)
    (reference : HavingStringRef) (op : EqualityOp) (expected : String) : Bool :=
  let comparison := match reference.operand with
    | .string field => FlatComparison.string op field expected
    | .enumeration operand => FlatComparison.enumeration op operand expected
  model.admitsTextComparisonIn (reference.origin.availableLevels candidateLevels outerLevels) comparison

private def FlatModel.admitsComparisonInputsIn (model : FlatModel)
    (comparison : FlatComparison) (leftScope rightScope : List RepeatableLevel) : Bool :=
  [(leftScope, comparison.inputFields.1), (rightScope, comparison.inputFields.2)].all fun (scope, fields) =>
    fields.all fun field => (model.lookupUniqueId field.id).toOption.any fun declaration =>
      field.matchesDecl declaration && declaration.fieldValueReadRefusal?.isNone &&
        repeatableScopeAvailable declaration.repeatableScope scope

/-- Authored clock grouping remains visible to the ordinary entry gate (spec/04). -/
def FlatTemporalOperand.havingEntry : FlatTemporalOperand → ComparisonEntryOperand
  | .fieldValue field => .field (.temporal field.kind)
  | .literalValue _ components => .literal (.temporal (components.family?.getD .date))
  | .timeValue _ => .literal (.temporal .time)
  | .localDateTimeValue _ _ => .literal (.temporal .dateTime)
  | .todayValue _ => .clock .date
  | .nowValue => .clock .dateTime
  | .baseYearValue _ _ => .literal .number
  | .baseYearRangeValue _ _ _ => .literal (.temporal .date)
  | .grouped source => .grouped source.havingEntry

def FlatTemporalOperand.havingComponents : FlatTemporalOperand → TemporalComponents
  | .fieldValue field => field.components
  | .literalValue _ components => components
  | .timeValue _ => TemporalComponents.time
  | .localDateTimeValue _ _ | .nowValue => TemporalComponents.now
  | .grouped source => source.havingComponents
  | _ => TemporalComponents.fullDate

private def FlatTemporalOperand.havingSourceAdmitted (model : FlatModel) : FlatTemporalOperand → Bool
  | .todayValue zone => zone == model.timeZoneId
  | .baseYearValue zone year | .baseYearRangeValue zone year _ =>
      zone == model.timeZoneId && model.baseYear == some year
  | .localDateTimeValue profile _ => ModelZone.ConcreteProfile.ofId? model.timeZoneId == some profile
  | .literalValue _ components => components.isDateLiteral
  | .grouped source => source.havingSourceAdmitted model
  | .fieldValue _ | .timeValue _ | .nowValue => true

def FlatModel.admitsHavingTemporalOperands (model : FlatModel) (op : TemporalComparisonOp)
    (left right : FlatTemporalOperand) : Bool :=
  comparisonConstantPairAllowed left.havingEntry right.havingEntry &&
    left.havingSourceAdmitted model && right.havingSourceAdmitted model &&
    op.admitsFormats model.hasBaseYear left.havingComponents right.havingComponents

/-- Each side is checked in its own environment; comparability and Boolean/Confirm restrictions retain their ordinary rules. -/
def FlatModel.admitsHavingSimpleComparison (model : FlatModel)
    (leftScope rightScope : List RepeatableLevel) : FlatComparison → Bool
  | .textFields _ left right =>
      match model.directComparableIn? leftScope left, model.directComparableIn? rightScope right with
      | some leftProfile, some rightProfile => directFieldComparisonAllowed leftProfile rightProfile
      | _, _ => false
  | comparison@(.boolean _ _ _) | comparison@(.confirm _ _)
      | comparison@(.booleanFields _ _ _) =>
      let shape := match comparison with
        | .booleanFields op left right => match left, right with
          | .boolean _, .boolean _ => true
          | .confirm _, .confirm _ => op == .notEqual
          | _, _ => false
        | _ => true
      shape && model.admitsComparisonInputsIn comparison leftScope rightScope
  | comparison@(.dateRange _ left right) =>
      model.dateRangeComparisonProfilesMatch left right &&
        model.admitsComparisonInputsIn comparison leftScope rightScope
  | comparison@(.temporal op left right) =>
      model.admitsHavingTemporalOperands op left right &&
        model.admitsComparisonInputsIn comparison leftScope rightScope
  | comparison@(.time op left right) =>
      !left.components.hasDate && !right.components.hasDate &&
        op.admitsFormats model.hasBaseYear left.components right.components &&
        model.admitsComparisonInputsIn comparison leftScope rightScope
  | _ => false

private def HavingGroupOperand.path? (operand : HavingGroupOperand) (model : FlatModel) : Option GroupPath :=
  match operand with
  | .field reference => (model.lookupUniqueId reference.field).toOption.map (·.path)
  | .group _ source => some source.reference.path

private def HavingGroupOperand.admitted (operand : HavingGroupOperand) (model : FlatModel)
    (candidateLevels outerLevels : List RepeatableLevel) : Bool :=
  match operand with
  | .field reference => (model.lookupUniqueId reference.field).toOption.any fun declaration =>
      repeatableScopeAvailable declaration.repeatableScope
        (reference.origin.availableLevels candidateLevels outerLevels)
  | .group origin source => model.groupContributesField source.reference.path &&
      source.admitted model (origin.availableLevels candidateLevels outerLevels)

private def HavingGroupOperand.isStarred : HavingGroupOperand → Bool
  | .field _ => false
  | .group _ source => source.starPath.isSome

private def havingGroupOperandsDisjoint (model : FlatModel) : List HavingGroupOperand → Bool
  | [] => true
  | first :: rest =>
      rest.all (fun other => match first.path? model, other.path? model with
        | some left, some right =>
            if left == right then first.isStarred || other.isStarred || first.origin != other.origin
            else !(left.isPrefixOf right || right.isPrefixOf left)
        | _, _ => false) && havingGroupOperandsDisjoint model rest

def CorrelatedHavingLeaf.wellFormedForEnvironments (model : FlatModel)
    (candidateLevels outerLevels : List RepeatableLevel) :
    CorrelatedHavingLeaf → Bool
  | .numeric comparison => comparison.havingAdmitted (HavingNumericAtomOf.wellFormedWith model candidateLevels outerLevels
      (fun unit left right => left.wellFormed model candidateLevels outerLevels &&
        right.wellFormed model candidateLevels outerLevels && left.admittedSourceSlot true && right.admittedSourceSlot true &&
        (left.components?).any (fun first => (right.components?).any (unit.admitsScalarDifference model.hasBaseYear first)))
      (fun part source => source.wellFormed model candidateLevels outerLevels &&
        source.admittedSourceSlot && source.components?.any (fun components => part.admitsComponents components model.hasBaseYear)))
  | .stringExpression comparison => comparison.wellFormed model candidateLevels outerLevels
  | .selectedComparison comparison => comparison.wellFormed model candidateLevels outerLevels
  | .temporalExpression comparison =>
      comparison.left.wellFormed model candidateLevels outerLevels &&
        comparison.right.wellFormed model candidateLevels outerLevels &&
        HavingTemporalExpression.comparisonAdmitted comparison.operator comparison.left comparison.right
  | .simpleComparison left right comparison =>
      model.admitsHavingSimpleComparison
        (left.availableLevels candidateLevels outerLevels)
        (right.availableLevels candidateLevels outerLevels) comparison
  | .compareStringLiteral op reference expected =>
      model.admitsHavingStringInEnvironment candidateLevels outerLevels reference op expected
  | .literalMembership origin _ source =>
      let scope := origin.availableLevels candidateLevels outerLevels
      match source with
      | .number field values =>
          !values.isEmpty && (model.lookupUniqueId field.id).toOption.any fun declaration =>
            (.number field : FlatField).matchesDecl declaration && declaration.repetitionBoundBy scope
      | .token operand values =>
          !values.isEmpty && match operand with
          | .string _ => model.directComparableIn? scope operand == some .plainString
          | .enumeration operand => (model.checkedEnumerationOperandIn? scope operand).any fun checked =>
              values.all (checked.declaration.literalAllowed checked.projection)
  | .dateValidity _ source => source.wellFormedForEnvironments model candidateLevels outerLevels
  | .dateRange source => source.wellFormedForEnvironments model candidateLevels outerLevels
  | .uniqueness source => source.wellFormedForEnvironments model candidateLevels outerLevels
  | .fieldMembership operator source =>
      source.wellFormedForEnvironments operator model candidateLevels outerLevels
  | .fieldFill _ references =>
      havingEntityListWellFormed model candidateLevels outerLevels references
  | .stringPattern _ reference _ =>
      model.admitsStringPatternField { id := reference.field } &&
        (model.lookupUniqueId reference.field).toOption.any fun declaration =>
          declaration.fieldValueReadRefusal?.isNone && repeatableScopeAvailable declaration.repeatableScope
            (reference.origin.availableLevels candidateLevels outerLevels)
  | .typeValidity _ reference name =>
      !name.isEmpty && (elaborateCustomFieldValidityOperand model reference.field).isOk &&
        (model.lookupUniqueId reference.field).toOption.any fun declaration =>
          declaration.fieldValueReadRefusal?.isNone && repeatableScopeAvailable declaration.repeatableScope
            (reference.origin.availableLevels candidateLevels outerLevels)
  | .groupPresence _ origin source =>
      source.dependencyKind == .conditionalPresence && source.starPath.isNone &&
        (HavingGroupOperand.group origin source).admitted model candidateLevels outerLevels
  | .groupFill operator first rest =>
      let operands := first :: rest
      (!operator.requiresMultipleOperands || !rest.isEmpty) &&
        havingGroupOperandsDisjoint model operands &&
        (!operator.requiresMultipleOperands || operands.all (fun operand => !operand.isStarred)) &&
        operands.all (fun operand => operand.admitted model candidateLevels outerLevels &&
          match operand with
          | .field _ => true
          | .group _ source => source.dependencyKind ==
              (if source.reference.isRoot && source.starPath.isNone then .conditionalPresence else .ordinaryList)) &&
        (operands.all fun
          | .field _ => true
          | .group _ source => !source.reference.isRoot ||
              (!operator.requiresMultipleOperands && rest.isEmpty))
  | .presence _ reference =>
      match model.lookupUniqueId reference.field with
      | .error _ => false
      | .ok declaration =>
          -- Presence reads any declared field, so this checks existence and environment
          -- availability only; there is no kind projection to satisfy.
          repeatableScopeAvailable declaration.repeatableScope
            (reference.origin.availableLevels candidateLevels outerLevels)

/-- Static environment admission for a resolved filter tree. Candidate references must be available in every topology-produced candidate environment; `$` references must be available in the captured rule environment. -/
def CorrelatedHaving.wellFormedForEnvironments (condition : CorrelatedHaving)
    (model : FlatModel) (candidateLevels outerLevels : List RepeatableLevel) : Bool :=
  condition.allLeaves fun leaf =>
    leaf.wellFormedForEnvironments model candidateLevels outerLevels

private def HavingNumberRef.reachesReopenedLevel (reference : HavingNumberRef)
    (model : FlatModel) (reopenedLevels : List RepeatableLevel) : Bool :=
  match reference.origin, model.lookupUniqueId reference.field.id with
  | .inner, .ok declaration =>
      declaration.repeatableScope.any reopenedLevels.contains
  | _, _ => false

private def HavingStringRef.reachesReopenedLevel (reference : HavingStringRef)
    (model : FlatModel) (reopenedLevels : List RepeatableLevel) : Bool :=
  match reference.origin, model.lookupUniqueId reference.field.id with
  | .inner, .ok declaration =>
      declaration.repeatableScope.any reopenedLevels.contains
  | _, _ => false

def CorrelatedHavingLeaf.reachesReopenedLevel (model : FlatModel)
    (reopenedLevels : List RepeatableLevel) : CorrelatedHavingLeaf → Bool
  | .numeric comparison =>
      (comparison.left.atoms ++ comparison.right.atoms).any fun
        | .groupCount operands => operands.any fun operand =>
            operand.origin == .inner && operand.bindingScope.any reopenedLevels.contains
        | .product source => source.presenceSlots.any fun slot =>
            slot.references.any (·.origin == .inner) &&
              (slot.bindingScope? model).any (fun scope => scope.any reopenedLevels.contains)
        | .collectionCount source => source.presenceSlots.any fun slot =>
            slot.references.any (·.origin == .inner) &&
              (slot.bindingScope? model).any (fun scope => scope.any reopenedLevels.contains)
        | .firstFilled slots | .aggregate _ slots => (HavingNumberAggregate.presenceSlots slots).any fun slot =>
            slot.references.any (·.origin == .inner) &&
              (slot.bindingScope? model).any (fun scope => scope.any reopenedLevels.contains)
        | .dateDifference _ left right | .dayDifference _ left right => (left.fields ++ right.fields).any fun reference => reference.origin == .inner &&
            (model.lookupUniqueId reference.field.id).toOption.any fun declaration =>
              declaration.repeatableScope.any reopenedLevels.contains
        | .dateTimeDifference _ left right => (left.fieldValues ++ right.fieldValues).any fun reference => reference.origin == .inner &&
            (model.lookupUniqueId reference.field.id).toOption.any fun declaration =>
              declaration.repeatableScope.any reopenedLevels.contains
        | .baseYear _ | .baseYearDatePart _ _ _ | .clockPart _ _ _ => false
        | .fieldValueAsNumber origin source => origin == .inner &&
            (model.certifiedFieldValueAsNumberDeclaration? source).any fun declaration =>
              declaration.repeatableScope.any reopenedLevels.contains
        | .field reference => reference.reachesReopenedLevel model reopenedLevels
        | .stringLength origin field | .stringRange origin field _ _ => origin == .inner &&
            (model.lookupUniqueId field.id).toOption.any fun declaration =>
              declaration.repeatableScope.any reopenedLevels.contains
        | .dateRangeBoundPart origin field _ _ => origin == .inner &&
            (model.lookupUniqueId field.id).toOption.any fun declaration =>
              declaration.repeatableScope.any reopenedLevels.contains
        | .temporalDifference _ left right =>
            left.reachesReopenedLevel model reopenedLevels || right.reachesReopenedLevel model reopenedLevels
        | .temporalExpressionPart _ source => source.reachesReopenedLevel model reopenedLevels
        | .temporalPart origin field _ _ => origin == .inner &&
            (model.lookupUniqueId field.id).toOption.any fun declaration =>
              declaration.repeatableScope.any reopenedLevels.contains
        | .repetition reference => reference.origin == .inner &&
            (reference.scope? model).any (·.any reopenedLevels.contains)
  | .stringExpression comparison => comparison.presenceSlots.any fun slot =>
      slot.references.any (·.origin == .inner) &&
        (slot.bindingScope? model).any (fun scope => scope.any reopenedLevels.contains)
  | .selectedComparison comparison => comparison.presenceSlots.any fun slot =>
      slot.references.any (·.origin == .inner) &&
        (slot.bindingScope? model).any (fun scope => scope.any reopenedLevels.contains)
  | .temporalExpression comparison => comparison.left.reachesReopenedLevel model reopenedLevels ||
      comparison.right.reachesReopenedLevel model reopenedLevels
  | .simpleComparison left right comparison =>
      ([(left, comparison.inputFields.1), (right, comparison.inputFields.2)]).any fun (origin, fields) =>
        origin == .inner && fields.any fun field =>
          (model.lookupUniqueId field.id).toOption.any fun declaration =>
            declaration.repeatableScope.any reopenedLevels.contains
  | .compareStringLiteral _ reference _ =>
      reference.reachesReopenedLevel model reopenedLevels
  | .literalMembership origin _ source =>
      origin == .inner && (model.lookupUniqueId source.field.id).toOption.any fun declaration =>
        declaration.repeatableScope.any reopenedLevels.contains
  | .dateValidity _ source => source.asTemporal.reachesReopenedLevel model reopenedLevels
  | .dateRange source => source.presenceSlots.any fun slot =>
      slot.references.any (fun ref => ref.origin == .inner) &&
        (slot.bindingScope? model).any (fun scope => scope.any reopenedLevels.contains)
  | .uniqueness source => source.presenceSlots.any fun slot =>
      slot.references.any (fun ref => ref.origin == .inner) &&
        (slot.bindingScope? model).any (fun scope => scope.any reopenedLevels.contains)
  | .fieldMembership _ source => source.presenceSlots.any fun slot =>
      slot.references.any (fun ref => ref.origin == .inner) &&
        (slot.bindingScope? model).any (fun scope => scope.any reopenedLevels.contains)
  | .fieldFill _ references => references.any fun slot =>
      slot.references.any (fun ref => ref.origin == .inner) &&
        (slot.bindingScope? model).any (fun scope => scope.any reopenedLevels.contains)
  | .groupPresence _ origin source =>
      origin == .inner && source.content.scope.any reopenedLevels.contains
  | .groupFill _ first rest => (first :: rest).any fun
      | .field reference => reference.origin == .inner &&
          (model.lookupUniqueId reference.field).toOption.any fun declaration =>
            declaration.repeatableScope.any reopenedLevels.contains
      | .group origin source => origin == .inner &&
          (source.starPath.map (·.bindingScope) |>.getD source.content.scope).any reopenedLevels.contains
  | .presence _ reference | .typeValidity _ reference _ | .stringPattern _ reference _ =>
      match reference.origin, model.lookupUniqueId reference.field with
      | .inner, .ok declaration =>
          declaration.repeatableScope.any reopenedLevels.contains
      | _, _ => false

/-- A legal star filter must depend on at least one unmarked reference at a level actually reopened by that starred operand. Bound-only or `$`-only trees do not establish an iteration to filter. -/
def CorrelatedHaving.reachesReopenedLevel (condition : CorrelatedHaving)
    (model : FlatModel) (reopenedLevels : List RepeatableLevel) : Bool :=
  condition.anyLeaf fun leaf => leaf.reachesReopenedLevel model reopenedLevels

end A12Kernel
