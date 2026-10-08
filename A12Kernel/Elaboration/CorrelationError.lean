import A12Kernel.Elaboration.RepetitionNotUniqueAdmission
import A12Kernel.Elaboration.ConstructedDateComponents
import A12Kernel.Elaboration.StringPattern
import A12Kernel.Elaboration.NumericSource
import A12Kernel.Elaboration.FieldEntityAdmission
import A12Kernel.Elaboration.Flat.Condition.Surface
import A12Kernel.Elaboration.LiteralComparisonDiagnostic
import A12Kernel.Elaboration.SingleGroup
import A12Kernel.Elaboration.CustomFieldValidity
import A12Kernel.Semantics.Correlation


namespace A12Kernel

inductive CorrelationElabError where
  | repetitionNotUnique (error : RepetitionNotUniqueElabError)
  | dateRange (diagnostic : KernelStaticDiagnostic)
  | dateComponents (error : ConstructedDateComponentsElabError)
  | uniquenessKind (path : List String)
  | uniquenessFormat (path : List String)
  | membershipKind (path : List String)
  | membershipBaseType (path : List String)
  | membershipStringLiteralKind (path : List String)
  | fieldFill (error : FieldEntityShapeElabError)
  | groupFill (error : FieldEntityShapeElabError)
  | groupPresence (error : FixedGroupReferenceError)
  | groupListStarNotAllowed
  | stringPattern (error : StringPatternConditionElabError)
  | typeValidityOperand (error : CustomFieldValidityOperandElabError)
  | typeValidityName (error : CustomFieldValidityElabError)
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
      String against a Number ([inbound](../../docs/sources/inbound-handbacks.md#inbound-2026-09-25c-filter-body)), a
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
  /-- A leaf outside the legacy numeric/repetition fragment. The public constructor name predates
      the richer checked-star route; the legacy adapter fails closed at this boundary. -/
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
  | literalScaleMismatch (path : List String) (fieldScale : Nat) (literalScale : Int)
  | constantNumericComparison
  | comparisonEntry (diagnostic : KernelStaticDiagnostic)
  | numericExpressionUnsupported
  | temporalPartPrecision (field : FieldId) (part : TemporalNumericPart)
  | numericOperandFieldNotNumber (path : List String) (actual : SurfaceScalarKind)
  | missingInner
  | disallowedConstructInFilter
  | missingOuter
  | errorGuardMismatch (errorPath guardPath : List String)
  /-- The repetition walk refuses this level because the reading rule does not bind the marked read. -/
  | outerLevelUnbound (path : List String) (unbound : UnboundOperandLevel)
  | dateRangeComponentsMismatch (leftPath rightPath : List String)
  | incoherentCore
  deriving Repr, DecidableEq

namespace CorrelationElabError

/-- The Kernel class one refused `Having` filter reports.

**The class is the filter's, not the wrapping operator's**, and that was the open question this
projection existed to answer. Measured as a fourteen-filter cross against three carriers — a
temporal extremum, a distinct count, and a filled-field count — every filter drew the identical
class on all three ([checkpoint](../../docs/sources/static-admission-and-class-probes.md#src-having-filter-comparison-and-scope-classes)).
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
  | .repetitionNotUnique error => error.diagnostic?
  | .disallowedConstructInFilter => some .disallowedConstructInFilterCondition
  | .comparisonEntry diagnostic => some diagnostic
  | .temporalPartPrecision _ _ => some .invalidDateType
  | .dateRange diagnostic => some diagnostic
  | .dateComponents (.extractorPartialPrecision _ _ _) => some .invalidDateType
  | .dateComponents .onlyConstantsUsed => some .onlyConstantsUsed
  | .dateComponents _ => none
  | .uniquenessKind _ | .uniquenessFormat _ => some .onlyStringEnumNumberDateAllowed
  | .membershipKind _ => some .onlyStringEnumNumberAllowed
  | .membershipBaseType _ => some .varyingTypesNotAllowed
  | .membershipStringLiteralKind _ => some .invalidTypesForComparison
  | .fieldFill error | .groupFill error => error.diagnostic?
  | .groupPresence error => error.diagnostic?
  | .groupListStarNotAllowed => some .noWildcardsGAllowed
  | .stringPattern error => error.diagnostic?
  | .typeValidityOperand error => error.diagnostic?
  | .typeValidityName .emptyTypeName => some .noEmpty
  | .dateRangeComponentsMismatch _ _ => some .invalidCompareToDateRange
  | .text (.enumerationOperand _ (.invalidLiteral _)) =>
      some .invalidStringConstantForEnumComparison
  | .text (.literalKindMismatch _ .boolean actual) => literalComparisonDiagnostic? .booleanLike actual
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
