import A12Kernel.Elaboration.Flat.Condition.Surface
import A12Kernel.Elaboration.LiteralComparisonDiagnostic
import A12Kernel.Elaboration.SingleGroup
import A12Kernel.Semantics.Correlation

/-! Authored correlated-filter forms and their static diagnostic vocabulary. -/

namespace A12Kernel

structure SurfaceHavingNumberRef where
  origin : HavingOrigin
  field : SurfaceFieldPath
  deriving Repr, DecidableEq

structure SurfaceHavingRepetitionRef where
  origin : HavingOrigin
  group : SurfaceGroupReference
  deriving Repr, DecidableEq

/-- A surface text filter reference. The path is kind-neutral; the consuming leaf decides which
    declaration projection must accept it. -/
structure SurfaceHavingStringRef where
  origin : HavingOrigin
  field : SurfaceFieldPath
  projectionRef : EnumerationProjectionRef := .stored
  deriving Repr, DecidableEq

/-- A surface presence filter reference. Presence accepts any declared field, so no kind projection
    stands between this path and the checked reference. -/
structure SurfaceHavingPresenceRef where
  origin : HavingOrigin
  field : SurfaceFieldPath
  deriving Repr, DecidableEq

inductive SurfaceHavingNumericAtom where
  | field (reference : SurfaceHavingNumberRef)
  | repetition (reference : SurfaceHavingRepetitionRef)
  deriving Repr, DecidableEq

inductive SurfaceCorrelatedHaving where
  | compareBoolean (op : EqualityOp) (reference : SurfaceHavingStringRef) (expected : Bool)
  | compareFields (op : SurfaceComparisonOp) (left right : SurfaceHavingStringRef)
  | numeric (op : SurfaceComparisonOp)
      (left right : AuthoredNumericExpr SurfaceHavingNumericAtom)
  /-- A String or Enumeration projection against a literal. The operator slot is an `EqualityOp`, so a text ordering
      comparison is unrepresentable here rather than refused during elaboration — the same
      treatment the ordinary String comparison surface gives it, and what `spec/04`'s
      equality-only rule states. The kernel's `MVK_INVALID_TYPE_FOR_COMPARISON` is a class this
      project models nowhere, so this is consistency rather than a local narrowing. -/
  | compareStrings (op : EqualityOp) (reference : SurfaceHavingStringRef)
      (expected : String)
  /-- `FieldFilled` or `FieldNotFilled`. The negative polarity is authorable here because the
      kernel admits it inside a filter without the iteration-negativity refusal that governs a
      rule's own condition. -/
  | presence (polarity : HavingPresencePolarity)
      (reference : SurfaceHavingPresenceRef)
  | and (left right : SurfaceCorrelatedHaving)
  /-- Disjunction inside a filter. The filter's condition is the ordinary condition production, so
      this is a strong-Kleene `Or` and a true disjunct dominates an unavailable one, keeping its
      row. The legacy one-group route still refuses it; only the star route admits it. -/
  | or (left right : SurfaceCorrelatedHaving)
  deriving Repr, DecidableEq

def SurfaceCorrelatedHaving.compareNumbers (op : SurfaceComparisonOp)
    (left right : SurfaceHavingNumberRef) : SurfaceCorrelatedHaving :=
  .numeric op (.atom (.field left)) (.atom (.field right))

def SurfaceCorrelatedHaving.compareRepetitions (op : SurfaceComparisonOp)
    (left right : SurfaceHavingRepetitionRef) : SurfaceCorrelatedHaving :=
  .numeric op (.atom (.repetition left)) (.atom (.repetition right))

def SurfaceCorrelatedHaving.compareNumberLiteral (op : SurfaceComparisonOp)
    (reference : SurfaceHavingNumberRef) (literal : DecodedNumericLiteral) : SurfaceCorrelatedHaving :=
  .numeric op (.atom (.field reference)) (.literal literal)

/-- The exact admitted validation shape: the error target is the outer Number guard, and the starred consumer is filtered by a genuinely correlated `Having`. Requiring `errorField = guardField` is this capsule's routing boundary, not a claim that every kernel rule has that shape. -/
structure SurfaceSingleCorrelatedRule where
  errorField : SurfaceFieldPath
  guardField : SurfaceFieldPath
  valueField : SurfaceSingleStarFieldPath
  having : SurfaceCorrelatedHaving
  deriving Repr, DecidableEq

inductive CorrelationElabError where
  | text (error : ElabError)
  | resolve (error : ResolveError)
  | invalidGroupReference (reference : SurfaceGroupPath)
  | wildcardOnRuleGroup
  | wildcardWithParentNavigation (parents : Nat)
  | fieldNotNumber (path : List String) (actual : SurfaceScalarKind)
  /-- A side of an ordering comparison that is not a Number, with the kind of its partner, which was
      read. The Kernel's ordering class reads the pair, so a refused side cannot name it alone. -/
  | orderingFieldNotNumber (path : List String) (actual : SurfaceScalarKind)
      (partner : SurfaceScalarKind)
  /-- A side of an equality or inequality that is not a Number, which this Number fragment refuses
      while the Kernel judges the pair: it draws `MVK_INVALID_COMPARE_TO_ENUM_OR_STRING` for a
      String against a Number ([inbound](../../docs/SOURCES.md#inbound-2026-09-25c-filter-body)), a
      class the ordering gates never draw. -/
  | equalityFieldNotNumber (path : List String) (actual : SurfaceScalarKind)
  /-- A field compared with a Number literal by `==` or `!=` that is not a Number. The partner is
      known to be a Number literal, so the class is the ordinary equality ladder's against a
      Number literal ([KF270](../../../a12-rulekit/docs/KERNEL-FINDINGS.md#kf270)), measured on the
      filter leaf at the String row
      ([checkpoint](../../docs/sources/having-filter-probes.md#src-having-number-leaf-grid)). -/
  | literalEqualityFieldNotNumber (path : List String) (actual : SurfaceScalarKind)
  /-- The reference does not name a String field carrying evaluated values. A raw-mode String
      declaration reaches this arm too, matching every other checked String consumer. -/
  | fieldNotStringValue (path : List String) (actual : SurfaceScalarKind)
  /-- A String **or presence** leaf reached a route that admits only the numeric and repetition
      leaves. The legacy one-group adapter is the only such route; it fails closed here rather than
      being widened. The name predates the presence leaf and is kept because it is a public
      constructor; both leaves report through it, and the public evaluator maps them together. -/
  | stringLeafOutsideStarRoute
  /-- A disjunctive filter reached the legacy one-group route, whose well-formedness predicate
      admits a conjunctive core only. The kernel admits `Or` in this position and the star route
      does too; this arm keeps the narrow route honest rather than silently reshaping the tree. -/
  | disjunctionOutsideStarRoute
  | fieldOutsideGroup (origin : HavingOrigin)
      (fieldPath expectedGroup : List String)
  /-- A leaf outside the filtered group beside a leaf reading one of its Number fields. The Kernel
      admits it as a constant ([`spec/07`](../../spec/07-repetition-and-iteration.md),
      [checkpoint](../../docs/sources/static-admission-and-class-probes.md#src-field-value-read-predictions)),
      which the legacy one-group route does not represent, so it refuses without a class. -/
  | constantLeafBesideIteratedLeaf (origin : HavingOrigin)
      (fieldPath expectedGroup : List String)
  | fieldScopeMismatch (fieldPath : List String)
      (expected actual : List RepeatableLevel)
  | fieldOutsideEnvironment (origin : HavingOrigin) (fieldPath : List String)
      (available actual : List RepeatableLevel)
  | repetitionGroupMismatch (expected actual : GroupPath)
  | unknownRepetitionGroup (path : GroupPath)
  | repetitionOutsideEnvironment (origin : HavingOrigin) (groupPath : GroupPath)
      (available : List RepeatableLevel) (actual : RepeatableLevel)
  | equalityScaleMismatch (leftPath : List String) (leftScale : Nat)
      (rightPath : List String) (rightScale : Nat)
  /-- An equality against a literal carrying more fraction digits than the field's scale. -/
  | literalScaleMismatch (path : List String) (fieldScale : Nat) (literalScale : Int)
  | constantNumericComparison
  | numericExpressionUnsupported
  | numericOperandFieldNotNumber (path : List String) (actual : SurfaceScalarKind)
  | missingInner
  | missingOuter
  | errorGuardMismatch (errorPath guardPath : List String)
  /-- A marked reference crossing a level the reading rule does not bind, with the level the walk
      refuses. -/
  | outerLevelUnbound (path : List String) (unbound : UnboundOperandLevel)
  | incoherentCore
  deriving Repr, DecidableEq

namespace CorrelationElabError

/-- The Kernel class one refused `Having` filter reports.

**The class is the filter's, not the wrapping operator's**, and that was the open question this
projection existed to answer. Measured as a fourteen-filter cross against three carriers — a
temporal extremum, a distinct count, and a filled-field count — every filter drew the identical
class on all three ([checkpoint](../../docs/SOURCES.md#src-having-filter-comparison-and-scope-classes)).
One shared projection is therefore right, where a per-carrier table would have been three copies of
one fact.

The two comparison arms carry kinds because **one arm reports several classes**. An ordering
comparison collapses every non-orderable kind into one class and reads both operands to decide it; a
String-literal comparison spreads the same kinds across four, and that column is the shared
literal-comparison ladder's `stringLike` row cell for cell — one Kernel comparison vocabulary that a
plain rule comparison reaches too, whatever route an assignment takes to it. Reading either column
off the other is wrong for six kinds of eight; the two temporal families are the only agreement.

A partner whose own read fails answers ahead of both kind gates, which are raised where the
comparison ends, so an ordering side is judged only against a partner that was read
([checkpoint](../../docs/sources/static-admission-and-class-probes.md#src-field-value-read-grid)).

The scope classes separate cleanly: a filter with no unmarked reference into a reopened level
reports `noIterationForWildcard`, a **different repeatable group's** unmarked field reference
reports `invalidIterationInFilterCondition`, and a star written *inside* the filter reports
`noWildcardsAllowed`. A marked reference to a level no host iteration binds meets the repetition
walk instead, `SurfaceCorrelatedHaving.unboundOuterReference?`, because it requires a captured host
binding ([fixed-reference checkpoint](../../docs/sources/having-filter-probes.md#src-fixed-repetition-having)
and [field-reference checkpoint](../../docs/sources/having-filter-probes.md#src-filter-reference-two-levels-above)).
The remaining arms are this project's own narrow-route boundaries, its
resolution routing, or unreachable by construction, and claim nothing. -/
def diagnostic? : CorrelationElabError → Option KernelStaticDiagnostic
  | .text (.enumerationOperand _ (.invalidLiteral _)) =>
      some .invalidStringConstantForEnumComparison
  | .text _ => none
  | .fieldNotNumber _ actual => numericComparisonDiagnostic? actual
  | .orderingFieldNotNumber _ actual partner => orderingComparisonDiagnostic? actual partner
  | .fieldNotStringValue _ actual =>
      literalComparisonDiagnostic? .stringLike actual
  | .fieldOutsideGroup _ _ _ | .missingInner => some .noIterationForWildcard
  | .fieldOutsideEnvironment .outer _ _ _ | .repetitionOutsideEnvironment .outer _ _ _ =>
      some .noWildcard
  | .fieldOutsideEnvironment .inner _ _ _ | .repetitionOutsideEnvironment .inner _ _ _ =>
      some .invalidIterationInFilterCondition
  | .wildcardOnRuleGroup | .wildcardWithParentNavigation _ =>
      some .noWildcardsAllowed
  | .equalityScaleMismatch _ _ _ _ | .literalScaleMismatch _ _ _ => some .invalidCompareDecimalPlaces
  | .constantNumericComparison => some .invalidCompareToConst
  | .literalEqualityFieldNotNumber _ actual => literalComparisonDiagnostic? .number actual
  | .outerLevelUnbound _ unbound => unbound.diagnostic?
  | .resolve error => error.diagnostic?
  -- Named rather than wildcarded. `stringLeafOutsideStarRoute` and `disjunctionOutsideStarRoute`
  -- are the legacy one-group route's own narrowness — the Kernel accepts both — and
  -- `equalityFieldNotNumber` is both routes' Number fragment's, its class depending on a pair it
  -- does not carry; the rest are routing or unreachable by construction.
  | .invalidGroupReference _ | .fieldScopeMismatch _ _ _ | .equalityFieldNotNumber _ _
  | .constantLeafBesideIteratedLeaf _ _ _
  | .repetitionGroupMismatch _ _ | .unknownRepetitionGroup _ | .stringLeafOutsideStarRoute
  | .disjunctionOutsideStarRoute
  | .missingOuter | .errorGuardMismatch _ _
  | .numericExpressionUnsupported | .numericOperandFieldNotNumber _ _
  | .incoherentCore => none

end CorrelationElabError

end A12Kernel
