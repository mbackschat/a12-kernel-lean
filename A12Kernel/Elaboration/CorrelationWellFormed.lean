import A12Kernel.Elaboration.HavingFieldValueList
import A12Kernel.Elaboration.Flat.FieldValueRead
import A12Kernel.Elaboration.SingleGroup
import A12Kernel.Elaboration.NumericSource
import A12Kernel.Elaboration.DateRangeBoundComponent
import A12Kernel.Semantics.Correlation

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


def repeatableScopeAvailable (required available : List RepeatableLevel) : Bool :=
  required.isPrefixOf available

/-- Resolve the complete binding scope from the model, including fixed-group ancestry.
    A forged fixed reference to a repeatable group cannot certify a constant index. -/
def HavingRepetitionRef.scope? (reference : HavingRepetitionRef) (model : FlatModel) :
    Option (List RepeatableLevel) :=
  match reference.source with
  | .repeatable level =>
      (model.repeatableGroupAtLevel? level).map fun group =>
        model.repeatableScopeForGroupPath group.path
  | .fixed path =>
      if model.hasGroupPath path && !model.repeatableGroups.any (fun group => group.path == path)
      then some (model.repeatableScopeForGroupPath path)
      else none

def HavingRepetitionRef.availableIn (reference : HavingRepetitionRef) (model : FlatModel)
    (candidateLevels outerLevels : List RepeatableLevel) : Bool :=
  (reference.scope? model).any fun scope =>
    repeatableScopeAvailable scope (reference.origin.availableLevels candidateLevels outerLevels)

/-- Filter comparisons share numeric admission while retaining the unsuppressed surface boundary. -/
def NumericComparisonOf.havingAdmitted (comparison : NumericComparisonOf HavingNumericAtom)
    (admitted : HavingNumericAtom → Bool) : Bool :=
  !comparison.suppressExactScaleWarning && comparison.admittedWith admitted HavingNumericAtom.summary

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
  | .simpleComparison _ _ _ | .compareStringLiteral _ _ _ | .fieldFill _ _ | .literalMembership _ _ _ | .fieldMembership _ _ | .presence _ _ => true

/-- Every leaf under the shared connective tree satisfies the static scale law. -/
def CorrelatedHaving.equalityScalesAgree (condition : CorrelatedHaving) : Bool :=
  condition.allLeaves CorrelatedHavingLeaf.equalityScalesAgree

def CorrelatedHavingLeaf.wellFormedForSingleGroup
    (model : FlatModel) (group : RepeatableGroupDecl) : CorrelatedHavingLeaf → Bool
  | .numeric comparison => comparison.havingAdmitted fun
      | .baseYear year | .baseYearDatePart year _ _ => model.baseYear == some year
      | .aggregate _ _ _ | .dateDifference _ _ _ | .dayDifference _ _ _ | .dateTimeDifference _ _ _ | .fieldValueAsNumber _ _ => false
      | .field reference => model.admitsSingleGroupNumber group reference.field
      | .dateRangeBoundPart _ _ _ _ | .stringLength _ _ | .stringRange _ _ _ _ | .temporalPart _ _ _ => false
      | .repetition reference => reference.source == .repeatable group.level
  -- The legacy one-group adapter admits only the leaves it was built for. The other
  -- leaves reach the checked-star route instead, so refusing them here fails closed rather than
  -- extending an adapter no current consumer needs them on.
  | .simpleComparison _ _ _ | .compareStringLiteral _ _ _ | .fieldFill _ _ | .literalMembership _ _ _ | .fieldMembership _ _ | .presence _ _ => false

def CorrelatedHaving.wellFormedForSingleGroup (condition : CorrelatedHaving)
    (model : FlatModel) (group : RepeatableGroupDecl) : Bool :=
  condition.allLeaves fun leaf => leaf.wellFormedForSingleGroup model group

private def FlatModel.admitsHavingNumberInEnvironment (model : FlatModel)
    (candidateLevels outerLevels : List RepeatableLevel)
    (reference : HavingNumberRef) : Bool :=
  match model.lookupUniqueId reference.field.id with
  | .error _ => false
  | .ok declaration =>
      declaration.toNumberField? == some reference.field &&
        repeatableScopeAvailable declaration.repeatableScope
          (reference.origin.availableLevels candidateLevels outerLevels)

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
  | comparison@(.temporal op (.fieldValue left) (.fieldValue right)) =>
      left.components.hasDate && right.components.hasDate &&
        op.admitsFormats model.hasBaseYear left.components right.components &&
        model.admitsComparisonInputsIn comparison leftScope rightScope
  | comparison@(.time op left right) =>
      !left.components.hasDate && !right.components.hasDate &&
        op.admitsFormats model.hasBaseYear left.components right.components &&
        model.admitsComparisonInputsIn comparison leftScope rightScope
  | _ => false

private def calendarSourceAdmitted (model : FlatModel)
    (candidateLevels outerLevels : List RepeatableLevel) :
    ResolvedDateDifferenceOperand HavingTemporalRef → Bool
  | .literal source anchorYear => source.admittedIn model anchorYear
  | .baseYear year _ => model.baseYear == some year
  | .today profile => ModelZone.ConcreteProfile.ofId? model.timeZoneId == some profile
  | .field reference => (model.lookupUniqueId reference.field.id).toOption.any fun declaration =>
      declaration.toTemporalField? == some reference.field &&
        repeatableScopeAvailable declaration.repeatableScope (reference.origin.availableLevels candidateLevels outerLevels)

def CorrelatedHavingLeaf.wellFormedForEnvironments (model : FlatModel)
    (candidateLevels outerLevels : List RepeatableLevel) :
    CorrelatedHavingLeaf → Bool
  | .numeric comparison => comparison.havingAdmitted fun
      | .aggregate _ first rest => !rest.isEmpty && havingAggregateUnique first rest &&
          (first :: rest).all (model.admitsHavingNumberInEnvironment candidateLevels outerLevels)
      | .dateDifference unit left right => unit.compatible model.hasBaseYear
          (left.componentsWith (·.field.components)) (right.componentsWith (·.field.components)) &&
          [left, right].all (calendarSourceAdmitted model candidateLevels outerLevels)
      | .dayDifference profile left right => ModelZone.ConcreteProfile.ofId? model.timeZoneId == some profile &&
          CalendarDayDifference.admittedBy (left.componentsWith (·.field.components)) &&
          CalendarDayDifference.admittedBy (right.componentsWith (·.field.components)) &&
          CalendarDayDifference.yearCompatible model.hasBaseYear
            (left.componentsWith (·.field.components)) (right.componentsWith (·.field.components)) &&
          [left, right].all (calendarSourceAdmitted model candidateLevels outerLevels)
      | .dateTimeDifference unit left right =>
          (left.dateTimeDifferenceComponentsWith? (·.field.components)).any fun first =>
            (right.dateTimeDifferenceComponentsWith? (·.field.components)).any fun second =>
              unit.compatible first second &&
                (left.fieldValues ++ right.fieldValues).all fun reference =>
                  (model.lookupUniqueId reference.field.id).toOption.any fun declaration =>
                    declaration.toTemporalField? == some reference.field &&
                      repeatableScopeAvailable declaration.repeatableScope (reference.origin.availableLevels candidateLevels outerLevels)
      | .baseYear year | .baseYearDatePart year _ _ => model.baseYear == some year
      | .fieldValueAsNumber origin source => (model.certifiedFieldValueAsNumberDeclaration? source).any fun declaration =>
          repeatableScopeAvailable declaration.repeatableScope (origin.availableLevels candidateLevels outerLevels)
      | .field reference => model.admitsHavingNumberInEnvironment candidateLevels outerLevels reference
      | .stringLength origin field => (model.lookupUniqueId field.id).toOption.any fun declaration =>
          declaration.toStringValueField? == some field && declaration.fieldValueReadRefusal?.isNone &&
            repeatableScopeAvailable declaration.repeatableScope (origin.availableLevels candidateLevels outerLevels)
      | .stringRange origin field start finish => validStringRange start finish &&
          (model.lookupUniqueId field.id).toOption.any fun declaration =>
            declaration.toStringValueField? == some field && declaration.fieldValueReadRefusal?.isNone &&
              repeatableScopeAvailable declaration.repeatableScope (origin.availableLevels candidateLevels outerLevels)
      | .dateRangeBoundPart origin field _ part => model.exposesDateRangeBoundPart field part &&
          (model.lookupUniqueId field.id).toOption.any fun declaration =>
            repeatableScopeAvailable declaration.repeatableScope (origin.availableLevels candidateLevels outerLevels)
      | .temporalPart origin field part => part.admittedBy field model.hasBaseYear &&
          (model.lookupUniqueId field.id).toOption.any fun declaration =>
            declaration.toTemporalField? == some field &&
              repeatableScopeAvailable declaration.repeatableScope (origin.availableLevels candidateLevels outerLevels)
      | .repetition reference => reference.availableIn model candidateLevels outerLevels
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
  | .fieldMembership operator source =>
      source.wellFormedForEnvironments operator model candidateLevels outerLevels
  | .fieldFill _ references =>
      references.length >= 2 && references.eraseDups.length == references.length &&
        references.all fun ref => (model.lookupUniqueId ref.field).toOption.any fun declaration =>
          repeatableScopeAvailable declaration.repeatableScope
            (ref.origin.availableLevels candidateLevels outerLevels)
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
        | .aggregate _ first rest => (first :: rest).any (·.reachesReopenedLevel model reopenedLevels)
        | .dateDifference _ left right | .dayDifference _ left right => (left.fields ++ right.fields).any fun reference => reference.origin == .inner &&
            (model.lookupUniqueId reference.field.id).toOption.any fun declaration =>
              declaration.repeatableScope.any reopenedLevels.contains
        | .dateTimeDifference _ left right => (left.fieldValues ++ right.fieldValues).any fun reference => reference.origin == .inner &&
            (model.lookupUniqueId reference.field.id).toOption.any fun declaration =>
              declaration.repeatableScope.any reopenedLevels.contains
        | .baseYear _ | .baseYearDatePart _ _ _ => false
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
        | .temporalPart origin field _ => origin == .inner &&
            (model.lookupUniqueId field.id).toOption.any fun declaration =>
              declaration.repeatableScope.any reopenedLevels.contains
        | .repetition reference => reference.origin == .inner &&
            (reference.scope? model).any (·.any reopenedLevels.contains)
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
  | .fieldMembership _ source => source.references.any fun ref =>
      ref.origin == .inner && (model.lookupUniqueId ref.field).toOption.any fun declaration =>
        declaration.repeatableScope.any reopenedLevels.contains
  | .fieldFill _ references => references.any fun ref =>
      ref.origin == .inner && (model.lookupUniqueId ref.field).toOption.any fun declaration =>
        declaration.repeatableScope.any reopenedLevels.contains
  | .presence _ reference =>
      match reference.origin, model.lookupUniqueId reference.field with
      | .inner, .ok declaration =>
          declaration.repeatableScope.any reopenedLevels.contains
      | _, _ => false

/-- A legal star filter must depend on at least one unmarked reference at a level actually reopened by that starred operand. Bound-only or `$`-only trees do not establish an iteration to filter. -/
def CorrelatedHaving.reachesReopenedLevel (condition : CorrelatedHaving)
    (model : FlatModel) (reopenedLevels : List RepeatableLevel) : Bool :=
  condition.anyLeaf fun leaf => leaf.reachesReopenedLevel model reopenedLevels

end A12Kernel
