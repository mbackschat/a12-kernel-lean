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

def HavingOrigin.availableLevels (origin : HavingOrigin)
    (candidateLevels outerLevels : List RepeatableLevel) : List RepeatableLevel :=
  match origin with
  | .inner => candidateLevels
  | .outer => outerLevels

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

/-- Operator-specific static scale law for one filter leaf: `==` and `!=` are gated, ordering is exempt. -/
def CorrelatedHavingLeaf.equalityScalesAgree : CorrelatedHavingLeaf → Bool
  | .compareNumbers op left right =>
      op.acceptsScales left.field right.field
  | .compareNumberLiteral op reference literal => op.acceptsLiteralScale reference.field literal
  | .compareRepetitions _ _ _ => true
  -- Neither text nor presence carries a declared scale, so the numeric scale law has nothing to
  -- say about either leaf.
  | .compareStringLiteral _ _ _ | .presence _ _ => true

/-- Every leaf under the shared connective tree satisfies the static scale law. -/
def CorrelatedHaving.equalityScalesAgree (condition : CorrelatedHaving) : Bool :=
  condition.allLeaves CorrelatedHavingLeaf.equalityScalesAgree

def CorrelatedHavingLeaf.wellFormedForSingleGroup
    (model : FlatModel) (group : RepeatableGroupDecl) : CorrelatedHavingLeaf → Bool
  | .compareNumbers op left right =>
      model.admitsSingleGroupNumber group left.field &&
      model.admitsSingleGroupNumber group right.field &&
      op.acceptsScales left.field right.field
  | .compareNumberLiteral op reference literal =>
      model.admitsSingleGroupNumber group reference.field &&
        op.acceptsLiteralScale reference.field literal
  | .compareRepetitions _ left right =>
      left.source == .repeatable group.level && right.source == .repeatable group.level
  -- The legacy one-group adapter admits only the leaves it was built for. The String and presence
  -- leaves reach the checked-star route instead, so refusing them here fails closed rather than
  -- extending an adapter no current consumer needs them on.
  | .compareStringLiteral _ _ _ | .presence _ _ => false

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

/-- The String counterpart. It uses the model-owned String **value** projection, so a raw-mode
    String declaration is refused here exactly as it is at every other checked String consumer. -/
private def FlatModel.admitsHavingStringInEnvironment (model : FlatModel)
    (candidateLevels outerLevels : List RepeatableLevel)
    (reference : HavingStringRef) : Bool :=
  match model.lookupUniqueId reference.field.id with
  | .error _ => false
  | .ok declaration =>
      declaration.toStringValueField? == some reference.field &&
        repeatableScopeAvailable declaration.repeatableScope
          (reference.origin.availableLevels candidateLevels outerLevels)

def CorrelatedHavingLeaf.wellFormedForEnvironments (model : FlatModel)
    (candidateLevels outerLevels : List RepeatableLevel) :
    CorrelatedHavingLeaf → Bool
  | .compareNumbers op left right =>
      model.admitsHavingNumberInEnvironment candidateLevels outerLevels left &&
        model.admitsHavingNumberInEnvironment candidateLevels outerLevels right &&
        op.acceptsScales left.field right.field
  | .compareNumberLiteral op reference literal =>
      model.admitsHavingNumberInEnvironment candidateLevels outerLevels reference &&
        op.acceptsLiteralScale reference.field literal
  | .compareRepetitions _ left right =>
      left.availableIn model candidateLevels outerLevels &&
        right.availableIn model candidateLevels outerLevels
  | .compareStringLiteral _ reference _ =>
      model.admitsHavingStringInEnvironment candidateLevels outerLevels reference
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
  | .compareNumbers _ left right =>
      left.reachesReopenedLevel model reopenedLevels ||
        right.reachesReopenedLevel model reopenedLevels
  | .compareRepetitions _ left right =>
      (left.origin == .inner && (left.scope? model).any (·.any reopenedLevels.contains)) ||
        (right.origin == .inner && (right.scope? model).any (·.any reopenedLevels.contains))
  | .compareNumberLiteral _ reference _ => reference.reachesReopenedLevel model reopenedLevels
  | .compareStringLiteral _ reference _ =>
      reference.reachesReopenedLevel model reopenedLevels
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
