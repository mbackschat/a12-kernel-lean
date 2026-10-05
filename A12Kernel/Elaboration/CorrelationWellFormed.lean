import A12Kernel.Elaboration.Flat.FieldValueRead
import A12Kernel.Elaboration.SingleGroup
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

/-- Only ordinary, unsuppressed numeric comparisons belong to the current filter surface. -/
def NumericComparisonOf.havingAdmitted (comparison : NumericComparisonOf HavingNumericAtom)
    (admitted : HavingNumericAtom → Bool) : Bool :=
  (match comparison.op with | .ordinary _ => true | .tolerance _ => false) &&
    !comparison.suppressExactScaleWarning && comparison.admittedWith admitted HavingNumericAtom.summary

/-- Operator-specific static scale law for one filter leaf: `==` and `!=` are gated, ordering is exempt. -/
def CorrelatedHavingLeaf.equalityScalesAgree : CorrelatedHavingLeaf → Bool
  | .numeric comparison =>
      match comparison.left.summary? HavingNumericAtom.summary,
          comparison.right.summary? HavingNumericAtom.summary with
      | some left, some right => comparison.op.acceptsScalesWithSuppression
          comparison.suppressExactScaleWarning left right
      | _, _ => false
  -- Text, Boolean/Confirm and presence carry no declared scale; their kind gates belong to
  -- wellFormedForEnvironments.
  | .simpleComparison _ _ _ | .compareStringLiteral _ _ _ | .fieldFill _ _ | .literalMembership _ _ _ | .presence _ _ => true

/-- Every leaf under the shared connective tree satisfies the static scale law. -/
def CorrelatedHaving.equalityScalesAgree (condition : CorrelatedHaving) : Bool :=
  condition.allLeaves CorrelatedHavingLeaf.equalityScalesAgree

def CorrelatedHavingLeaf.wellFormedForSingleGroup
    (model : FlatModel) (group : RepeatableGroupDecl) : CorrelatedHavingLeaf → Bool
  | .numeric comparison => comparison.havingAdmitted fun
      | .field reference => model.admitsSingleGroupNumber group reference.field
      | .repetition reference => reference.source == .repeatable group.level
  -- The legacy one-group adapter admits only the leaves it was built for. The other
  -- leaves reach the checked-star route instead, so refusing them here fails closed rather than
  -- extending an adapter no current consumer needs them on.
  | .simpleComparison _ _ _ | .compareStringLiteral _ _ _ | .fieldFill _ _ | .literalMembership _ _ _ | .presence _ _ => false

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

def CorrelatedHavingLeaf.wellFormedForEnvironments (model : FlatModel)
    (candidateLevels outerLevels : List RepeatableLevel) :
    CorrelatedHavingLeaf → Bool
  | .numeric comparison => comparison.havingAdmitted fun
      | .field reference => model.admitsHavingNumberInEnvironment candidateLevels outerLevels reference
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
        | .field reference => reference.reachesReopenedLevel model reopenedLevels
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
