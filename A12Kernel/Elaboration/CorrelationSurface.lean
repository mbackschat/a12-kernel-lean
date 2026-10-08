import A12Kernel.Elaboration.ConstructedDateComponents
import A12Kernel.Elaboration.StringPattern
import A12Kernel.Elaboration.NumericSource
import A12Kernel.Elaboration.FieldEntityAdmission
import A12Kernel.Elaboration.Flat.Condition.Surface
import A12Kernel.Elaboration.LiteralComparisonDiagnostic
import A12Kernel.Elaboration.SingleGroup
import A12Kernel.Elaboration.CustomFieldValidity
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

structure SurfaceHavingTemporalRef where
  origin : HavingOrigin
  field : SurfaceFieldPath
  deriving Repr, DecidableEq

inductive SurfaceHavingDateComponent where
  | field (reference : SurfaceHavingPresenceRef)
  | constant (source : String)
  | extractor (part : DateNumericPart) (reference : SurfaceHavingPresenceRef)
  | baseYearExtractor (source : BaseYearDateSource) (part : DateNumericPart)
  | clockExtractor (point : ConstructedDatePointInTime) (part : DateNumericPart)
  deriving Repr, DecidableEq

abbrev SurfaceHavingDateComponents := SurfaceConstructedDateComponents SurfaceHavingDateComponent

def SurfaceHavingDateComponents.sources (source : SurfaceHavingDateComponents) : List SurfaceHavingDateComponent :=
  [source.day, source.month] ++ match source.year with
    | .complete year => [year]
    | .baseYear => []
    | .centuryAndShortYear century shortYear => [century, shortYear]

def SurfaceHavingDateComponents.references (source : SurfaceHavingDateComponents) : List SurfaceHavingPresenceRef :=
  source.sources.filterMap fun
    | .field reference | .extractor _ reference => some reference
    | _ => none

inductive SurfaceHavingTimeComponent where
  | field (reference : SurfaceHavingPresenceRef)
  | constant (value : String)
  | extractor (part : TimeNumericPart) (reference : SurfaceHavingPresenceRef)
  | nowExtractor (part : TimeNumericPart)
  deriving Repr, DecidableEq

abbrev SurfaceHavingTimeComponents := TimeComponentPrefix SurfaceHavingTimeComponent

/-- Constructor operands retain an origin at every field, including mixed captured/candidate reads. -/
inductive SurfaceHavingTemporalExpression where
  | field (reference : SurfaceHavingTemporalRef)
  | rangeBound (reference : SurfaceHavingTemporalRef) (bound : DateRangeBound)
  | timeConstruction (components : SurfaceHavingTimeComponents)
  | dateConstruction (components : SurfaceHavingDateComponents)
  | dateLiteral (source : AuthoredDateLiteral)
  | timeLiteral (value : TimeOfDay)
  | dateTimeLiteral (value : LocalDateTime)
  | today
  | now
  | baseYearBound (bound : BaseYearRangeEndpoint)
  | grouped (source : SurfaceHavingTemporalExpression)
  | dateTime (date time : SurfaceHavingTemporalExpression)
  | dateFromDateTime (source : SurfaceHavingTemporalExpression)
  | timeFromDateTime (source : SurfaceHavingTemporalExpression)
  deriving Repr, DecidableEq

def SurfaceHavingTemporalExpression.fields : SurfaceHavingTemporalExpression → List SurfaceHavingTemporalRef
  | .field reference | .rangeBound reference _ => [reference]
  | .timeConstruction components => components.sources.filterMap fun
      | .field ref | .extractor _ ref => some { origin := ref.origin, field := ref.field }
      | _ => none
  | .dateConstruction components => components.references.map fun ref => { origin := ref.origin, field := ref.field }
  | .grouped source | .dateFromDateTime source | .timeFromDateTime source => source.fields
  | .dateTime date time => date.fields ++ time.fields
  | _ => []

inductive SurfaceHavingNumericAtom where
  | aggregate (op : NumericAggregateOp) (source : SurfaceHavingEntitySource)
  | dateDifference (unit : DateDifferenceUnit) (left right : SurfaceDateDifferenceOperand SurfaceHavingTemporalRef)
  | dayDifference (left right : SurfaceDateDifferenceOperand SurfaceHavingTemporalRef)
  | dateTimeDifference (unit : DateTimeSubdayUnit) (left right : SurfaceDateDifferenceOperand SurfaceHavingTemporalRef)
  | baseYear
  | baseYearDatePart (source : BaseYearDateSource) (part : DateNumericPart)
  | clockPart (source : HavingClockSource) (part : TemporalNumericPart)
  | fieldValueAsNumber (reference : SurfaceHavingStringRef)
  | field (reference : SurfaceHavingNumberRef)
  | stringLength (origin : HavingOrigin) (field : SurfaceFieldPath)
  | stringRange (origin : HavingOrigin) (field : SurfaceFieldPath) (start finish : Nat)
  | dateRangeBoundPart (origin : HavingOrigin) (field : SurfaceFieldPath) (bound : DateRangeBound) (part : DateNumericPart)
  | temporalExpressionPart (part : TemporalNumericPart) (source : SurfaceHavingTemporalExpression)
  | temporalPart (origin : HavingOrigin) (field : SurfaceFieldPath) (part : TemporalNumericPart)
  | repetition (reference : SurfaceHavingRepetitionRef)
  deriving Repr, DecidableEq

/-- Temporal operands preserve grouping for the ordinary constant-pair gate (spec/04). -/
inductive SurfaceHavingTemporalOperand where
  | field (reference : SurfaceHavingStringRef)
  | constant (source : SurfaceDateDifferenceOperand Empty)
  | timeLiteral (value : TimeOfDay)
  | dateTimeLiteral (value : LocalDateTime)
  | grouped (source : SurfaceHavingTemporalOperand)
  deriving Repr, DecidableEq

def SurfaceHavingTemporalOperand.fields : SurfaceHavingTemporalOperand → List SurfaceHavingStringRef
  | .field reference => [reference]
  | .grouped source => source.fields
  | _ => []

inductive SurfaceCorrelatedHaving where
  | compareBoolean (op : EqualityOp) (reference : SurfaceHavingStringRef) (expected : Bool)
  | compareFields (op : SurfaceComparisonOp) (left right : SurfaceHavingStringRef)
  | compareTemporalExpression (op : SurfaceComparisonOp) (left right : SurfaceHavingTemporalExpression)
  | compareTemporal (op : SurfaceComparisonOp) (left right : SurfaceHavingTemporalOperand)
  | tolerance (range : NumericToleranceRange)
      (left right : AuthoredNumericExpr SurfaceHavingNumericAtom)
  | numeric (op : SurfaceComparisonOp)
      (left right : AuthoredNumericExpr SurfaceHavingNumericAtom)
  /-- A String or Enumeration projection against a literal retains an equality-only operator
      (spec/04). Text-literal ordering is therefore unrepresentable on this filter surface;
      SG17 owns integration of the existing comparison-entry refusal into this route. -/
  | compareStrings (op : EqualityOp) (reference : SurfaceHavingStringRef)
      (expected : String)
  | literalList (quantifier : ValueListQuantifier) (subjects : SurfaceHavingEntitySource)
      (values : List String)
  | dateValidity (operation : ConstructedDateValidityOp) (source : SurfaceHavingDateComponents)
  | uniqueness (source : SurfaceHavingEntitySource)
  | fieldMembership (operator : ComputationValueListOperator)
      (subjects members : SurfaceHavingEntitySource)
  | literalMembership (operator : ValueListMembershipOp) (reference : SurfaceHavingStringRef)
      (values : Sum (List Int) (List String))
  | fieldFill (operator : FieldFillQuantifier) (source : SurfaceHavingEntitySource)
  /-- `FieldFilled` or `FieldNotFilled`. The negative polarity is authorable here because the
      kernel admits it inside a filter without the iteration-negativity refusal that governs a
      rule's own condition. -/
  | presence (polarity : HavingPresencePolarity)
      (reference : SurfaceHavingPresenceRef)
  | stringPattern (operation : StringPatternOp) (reference : SurfaceHavingPresenceRef) (source : String)
  | typeValidity (operation : CustomFieldValidityOp) (reference : SurfaceHavingPresenceRef) (name : String)
  | groupPresence (operator : GroupPresenceOperator) (origin : HavingOrigin)
      (reference : SurfaceGroupReference)
  | groupFill (operator : GroupFillQuantifier)
      (first : HavingOrigin × SurfaceGroupReference) (rest : List (HavingOrigin × SurfaceGroupReference))
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
  | dateComponents (error : ConstructedDateComponentsElabError)
  | uniquenessKind (path : List String)
  | uniquenessFormat (path : List String)
  | membershipKind (path : List String)
  | membershipBaseType (path : List String)
  | membershipStringLiteralKind (path : List String)
  | fieldFill (error : FieldEntityShapeElabError)
  | groupFill (error : FieldEntityShapeElabError)
  | groupPresence (error : FixedGroupReferenceError)
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
  | dateRangeComponentsMismatch (leftPath rightPath : List String)
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
  | .dateComponents (.extractorPartialPrecision _ _ _) => some .invalidDateType
  | .dateComponents .onlyConstantsUsed => some .onlyConstantsUsed
  | .dateComponents _ => none
  | .uniquenessKind _ | .uniquenessFormat _ => some .onlyStringEnumNumberDateAllowed
  | .membershipKind _ => some .onlyStringEnumNumberAllowed
  | .membershipBaseType _ => some .varyingTypesNotAllowed
  | .membershipStringLiteralKind _ => some .invalidTypesForComparison
  | .fieldFill error | .groupFill error => error.diagnostic?
  | .groupPresence error => error.diagnostic?
  | .stringPattern error => error.diagnostic?
  | .typeValidityOperand error => error.diagnostic?
  | .typeValidityName .emptyTypeName => some .noEmpty
  | .dateRangeComponentsMismatch _ _ => some .invalidCompareToDateRange
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

/-- The first marked reference of an authored filter, in authored order, crossing a level the
    reading rule does not bind, with the level the walk refuses. A marked reference reads the rule's
    own environment, so it meets the walk like any read and its class is placed by the error field:
    measured on a keyed and an unkeyed level beside the error field's group
    ([checkpoint](../../docs/sources/group-list-and-capacity-probes.md#src-walk-batch-reading-scope)).
    A reference that does not resolve is left to the filter's own resolution. -/
def SurfaceCorrelatedHaving.unboundOuterReference? (model : FlatModel)
    (declaringGroup writtenGroup : GroupPath)
    (bound : List RepeatableLevel := model.repeatableScopeForGroupPath declaringGroup) :
    SurfaceCorrelatedHaving → Option (List String × UnboundOperandLevel)
  | .numeric _ left right | .tolerance _ left right =>
      (left.atoms ++ right.atoms).findSome? fun
        | .aggregate _ source => (source.first :: source.rest).findSome? entity
        | .dateDifference _ left right | .dayDifference left right =>
            (left.fields ++ right.fields).findSome? fun reference => field reference.origin reference.field
        | .dateTimeDifference _ left right =>
            (left.fields ++ right.fields).findSome? fun reference => field reference.origin reference.field
        | .temporalExpressionPart _ source => source.fields.findSome? fun reference => field reference.origin reference.field
        | .baseYear | .baseYearDatePart _ _ | .clockPart _ _ => none
        | .fieldValueAsNumber reference => field reference.origin reference.field
        | .field reference => field reference.origin reference.field
        | .dateRangeBoundPart origin reference _ _ | .stringLength origin reference | .stringRange origin reference _ _ | .temporalPart origin reference _ => field origin reference
        | .repetition reference => group reference.origin reference.group
  | .compareFields _ left right =>
      (field left.origin left.field).orElse fun _ => field right.origin right.field
  | .compareBoolean _ reference _ | .compareStrings _ reference _ => field reference.origin reference.field
  | .compareTemporalExpression _ left right =>
      (left.fields ++ right.fields).findSome? fun reference => field reference.origin reference.field
  | .compareTemporal _ left right =>
      (left.fields ++ right.fields).findSome? fun reference => field reference.origin reference.field
  | .literalMembership _ reference _ => field reference.origin reference.field
  | .fieldMembership _ subjects members =>
      (subjects.first :: subjects.rest ++ members.first :: members.rest).findSome? entity
  | .dateValidity _ source => source.references.findSome? fun ref => field ref.origin ref.field
  | .uniqueness source | .fieldFill _ source | .literalList _ source _ =>
      (source.first :: source.rest).findSome? entity
  | .presence _ reference | .typeValidity _ reference _ | .stringPattern _ reference _ => field reference.origin reference.field
  | .groupPresence _ origin reference => group origin reference
  | .groupFill _ first rest => (first :: rest).findSome? fun (origin, reference) => group origin reference
  | .and left right | .or left right =>
      (left.unboundOuterReference? model declaringGroup writtenGroup bound).orElse fun _ =>
        right.unboundOuterReference? model declaringGroup writtenGroup bound
where
  entity (ref : SurfaceHavingEntityOperand) : Option (List String × UnboundOperandLevel) := do
    guard (ref.origin == .outer)
    let (path, scope) ← ref.bindingRead? model declaringGroup
    let unbound ← model.unboundReadLevel? declaringGroup writtenGroup scope bound
    pure (path, unbound)
  field (origin : HavingOrigin) (reference : SurfaceFieldPath) :
      Option (List String × UnboundOperandLevel) := do
    guard (origin == .outer)
    let declaration ← (model.resolveFieldDeclarationUnchecked declaringGroup reference).toOption
    let unbound ← model.unboundReadLevel? declaringGroup writtenGroup declaration.repeatableScope bound
    pure (declaration.path, unbound)
  group (origin : HavingOrigin) (reference : SurfaceGroupReference) :
      Option (List String × UnboundOperandLevel) := do
    guard (origin == .outer)
    let resolved ← (reference.resolveAgainst declaringGroup).toOption
    let unbound ← model.unboundReadLevel? declaringGroup writtenGroup
      (model.repeatableScopeForGroupPath resolved.path) bound
    pure (resolved.path, unbound)

/-- Refuse a filter whose marked reference the walk refuses. Callers ask it before the filter's own
    checks; no row measures a filter failing both, so that order is this project's choice. -/
def SurfaceCorrelatedHaving.requireOuterReferencesBound (model : FlatModel)
    (declaringGroup writtenGroup : GroupPath) (having : SurfaceCorrelatedHaving)
    (bound : List RepeatableLevel := model.repeatableScopeForGroupPath declaringGroup) :
    Except CorrelationElabError Unit :=
  match having.unboundOuterReference? model declaringGroup writtenGroup bound with
  | some (path, unbound) => throw (.outerLevelUnbound path unbound)
  | none => pure ()

end A12Kernel
