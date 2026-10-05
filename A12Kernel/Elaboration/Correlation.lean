import A12Kernel.Elaboration.Flat.Condition.Surface
import A12Kernel.Elaboration.LiteralComparisonDiagnostic
import A12Kernel.Elaboration.Flat.FieldValueRead
import A12Kernel.Elaboration.SingleGroup
import A12Kernel.Elaboration.StarPath
import A12Kernel.Elaboration.CorrelationWellFormed
import A12Kernel.Semantics.Correlation

/-! # A12Kernel.Elaboration.Correlation — checked lowering for repeatable filters

The established whole-rule route admits exactly one repeatable group, one starred direct-child Number field, an outer `FieldFilled` Number guard, and a correlated `Having` made from shared numeric-expression comparisons and conjunction. The general-star route also admits String/Enumeration literal equality, presence and disjunction after a checked star path has fixed the complete candidate environment. Both routes accept only references available from that candidate environment or the captured rule environment and require an ordinary reference to reach a reopened level.
-/

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
  | .numeric _ left right =>
      (left.atoms ++ right.atoms).findSome? fun
        | .field reference => field reference.origin reference.field
        | .repetition reference => group reference.origin reference.group
  | .compareStrings _ reference _ => field reference.origin reference.field
  | .presence _ reference => field reference.origin reference.field
  | .and left right | .or left right =>
      (left.unboundOuterReference? model declaringGroup writtenGroup bound).orElse fun _ =>
        right.unboundOuterReference? model declaringGroup writtenGroup bound
where
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

private def SurfaceComparisonOp.toCorrelation : SurfaceComparisonOp → CorrelationComparisonOp
  | .equal => .equal
  | .notEqual => .notEqual
  | .less => .lessThan
  | .lessEqual => .lessEqual
  | .greater => .greaterThan
  | .greaterEqual => .greaterEqual

private structure ResolvedNumberRef where
  declaration : FlatFieldDecl
  core : HavingNumberRef

/-- Whether a resolved filter uses only leaves and conjunction. This is narrower than the authored
surface, which also carries `.or`. The legacy one-group route is the only consumer, at both its
elaboration arm and its own well-formedness predicate; the star route takes the full surface. -/
def CorrelatedHaving.isConjunctive (condition : CorrelatedHaving) : Bool :=
  match condition with
  | .leaf _ => true
  | .and left right =>
      CorrelatedHaving.isConjunctive left &&
        CorrelatedHaving.isConjunctive right
  | .or _ _ => false

private def CorrelationElabError.ofSingleGroup (origin : HavingOrigin) :
    SingleGroupElabError → CorrelationElabError
  | .resolve error => .resolve error
  | .invalidGroupReference reference => .invalidGroupReference reference
  | .wildcardOnRuleGroup => .wildcardOnRuleGroup
  | .wildcardWithParentNavigation parents => .wildcardWithParentNavigation parents
  | .fieldNotNumber path actual => .fieldNotNumber path actual
  | .fieldOutsideGroup fieldPath expectedGroup =>
      .fieldOutsideGroup origin fieldPath expectedGroup
  | .fieldScopeMismatch fieldPath expected actual =>
      .fieldScopeMismatch fieldPath expected actual

/-- Class a filter body's read whose path names a group. The body's reader asks no environment as it
    resolves an unmarked reference, so such a path meets the group gate directly. -/
private def FlatModel.havingGroupRead (model : FlatModel) (declaringGroup : GroupPath)
    (reference : SurfaceFieldPath) : Unit → Option (GroupPath × Option UnboundOperandLevel) :=
  fun _ => (model.groupNamedBy? declaringGroup reference).map (·, none)

/-- The single-group route's body read with its placement requirement, that the field sit directly
    in the filtered group. The read's gates and the comparison's own classes were already asked of
    the whole body by `resolveHavingNumberRead`. -/
private def FlatModel.resolveHavingNumberInGroup (model : FlatModel)
    (declaringGroup : GroupPath) (group : RepeatableGroupDecl)
    (origin : HavingOrigin) (reference : SurfaceFieldPath) :
    Except CorrelationElabError ResolvedNumberRef := do
  let (declaration, field) ← model.resolveNumberInGroup declaringGroup group reference
    |>.mapError (.ofSingleGroup origin)
  pure { declaration, core := { origin, field } }

private def resolveHavingRepetitionInGroup
    (declaringGroup : GroupPath) (group : RepeatableGroupDecl)
    (origin : HavingOrigin) (reference : SurfaceGroupReference) :
    Except CorrelationElabError HavingRepetitionRef := do
  let resolved ← reference.resolveAgainst declaringGroup |>.mapError (.ofSingleGroup origin)
  if resolved.path != group.path then
    throw (.repetitionGroupMismatch group.path resolved.path)
  pure { origin, source := .repeatable group.level }

/-- The per-leaf reference resolvers one filter route supplies. They travel as a bundle because
    each route chooses all of them together, and a route that admits no String or presence leaf
    supplies a refusing resolver rather than a different combinator. -/
private structure HavingLeafResolvers where
  number : HavingOrigin → SurfaceFieldPath →
    Except CorrelationElabError ResolvedNumberRef
  repetition : HavingOrigin → SurfaceGroupReference →
    Except CorrelationElabError HavingRepetitionRef
  string : EqualityOp → SurfaceHavingStringRef → String →
    Except CorrelationElabError HavingStringRef
  presence : HavingOrigin → SurfaceFieldPath →
    Except CorrelationElabError HavingPresenceRef

/-- Both sides of an ordering comparison, a kind refusal carrying its partner's kind. A side whose
    read fails answers ahead of both kind gates, the left one first, so a left kind refusal meeting a
    right read failure raises the right's error. -/
private def orderingSides (left right : Except CorrelationElabError ResolvedNumberRef) :
    Except CorrelationElabError (ResolvedNumberRef × ResolvedNumberRef) :=
  match left, right with
  | .ok leftResolved, .ok rightResolved => pure (leftResolved, rightResolved)
  | .error (.fieldNotNumber path actual), .ok _ =>
      throw (.orderingFieldNotNumber path actual .number)
  | .error (.fieldNotNumber path actual), .error (.fieldNotNumber _ partner) =>
      throw (.orderingFieldNotNumber path actual partner)
  | .error (.fieldNotNumber _ _), .error error => throw error
  | .error error, _ => throw error
  | .ok _, .error (.fieldNotNumber path actual) =>
      throw (.orderingFieldNotNumber path actual .number)
  | .ok _, .error error => throw error

private def elaborateHavingNumeric (resolvers : HavingLeafResolvers)
    (op : SurfaceComparisonOp) (left right : AuthoredNumericExpr SurfaceHavingNumericAtom) :
    Except CorrelationElabError CorrelatedHaving := do
  match left, right with
  | .atom (.field left), .atom (.field right) => do
      let coreOp := op.toCorrelation
      let resolve (reference : SurfaceHavingNumberRef) :=
        resolvers.number reference.origin reference.field
      let (leftResolved, rightResolved) ← match coreOp with
        | .lessThan | .lessEqual | .greaterThan | .greaterEqual =>
            orderingSides (resolve left) (resolve right)
        | .equal | .notEqual => do
            let side (reference : SurfaceHavingNumberRef) :=
              (resolve reference).mapError fun
                | .fieldNotNumber path actual => .equalityFieldNotNumber path actual
                | error => error
            pure (← side left, ← side right)
      if !coreOp.acceptsScales leftResolved.core.field rightResolved.core.field then
        throw (.equalityScaleMismatch
          leftResolved.declaration.path leftResolved.core.field.info.scale
          rightResolved.declaration.path rightResolved.core.field.info.scale)
      pure (.compareNumbers coreOp leftResolved.core rightResolved.core)
  | .atom (.field reference), .literal literal
  | .literal literal, .atom (.field reference) => do
      let coreOp := op.toCorrelation
      let resolved ← (resolvers.number reference.origin reference.field).mapError fun
        | .fieldNotNumber path actual =>
            match coreOp with
            | .equal | .notEqual => .literalEqualityFieldNotNumber path actual
            | _ => .orderingFieldNotNumber path actual .number
        | error => error
      if !coreOp.acceptsLiteralScale resolved.core.field literal then
        throw (.literalScaleMismatch resolved.declaration.path resolved.core.field.info.scale
          literal.authoredScale)
      pure (.leaf (.numeric
        { op := .ordinary coreOp.toNumeric
          left := left.map (fun _ => .field resolved.core)
          right := right.map (fun _ => .field resolved.core) }))
  | .atom (.repetition left), .atom (.repetition right) => do
      let coreOp := op.toCorrelation
      pure (.compareRepetitions coreOp
        (← resolvers.repetition left.origin left.group)
        (← resolvers.repetition right.origin right.group))
  | _, _ =>
      let resolve : SurfaceHavingNumericAtom → Except CorrelationElabError HavingNumericAtom
        | .field reference => do
            let resolved ← (resolvers.number reference.origin reference.field).mapError fun
              | .fieldNotNumber path actual => .numericOperandFieldNotNumber path actual
              | error => error
            pure (.field resolved.core)
        | .repetition reference =>
            (.repetition ·) <$> resolvers.repetition reference.origin reference.group
      let leftCore ← left.mapM resolve
      let rightCore ← right.mapM resolve
      if leftCore.isImmediateLiteral && rightCore.isImmediateLiteral then
        throw .constantNumericComparison
      let comparison : NumericComparisonOf HavingNumericAtom :=
        { op := .ordinary op.toCorrelation.toNumeric, left := leftCore, right := rightCore }
      if !comparison.havingAdmitted (fun _ => true) then
        throw .numericExpressionUnsupported
      pure (.leaf (.numeric comparison))

private def elaborateHavingCoreWith (resolvers : HavingLeafResolvers) :
    SurfaceCorrelatedHaving → Except CorrelationElabError CorrelatedHaving
  | .numeric op left right => elaborateHavingNumeric resolvers op left right
  | .compareStrings op reference expected => do
      pure (.compareStringLiteral op
        (← resolvers.string op reference expected) expected)
  | .presence polarity reference => do
      pure (.presence polarity
        (← resolvers.presence reference.origin reference.field))
  | .and left right => do
      pure (.and (← elaborateHavingCoreWith resolvers left)
        (← elaborateHavingCoreWith resolvers right))
  | .or left right => do
      pure (.or (← elaborateHavingCoreWith resolvers left)
        (← elaborateHavingCoreWith resolvers right))

/-- A filter body's bracketed read on the single-group route, without the route's placement
    requirement: the read's gates, then the Number kind the leaf needs. -/
private def FlatModel.resolveHavingNumberRead (model : FlatModel) (declaringGroup : GroupPath)
    (origin : HavingOrigin) (reference : SurfaceFieldPath) :
    Except CorrelationElabError ResolvedNumberRef := do
  let declaration ← (checkFieldValueRead (model.resolveFieldDeclarationUnchecked declaringGroup reference)
    (model.havingGroupRead declaringGroup reference)).mapError .resolve
  match declaration.toNumberField? with
  | some field => pure { declaration, core := { origin, field } }
  | none => throw (.fieldNotNumber declaration.path declaration.policy.kind.surfaceKind)

/-- Whether an unmarked leaf of the body reads a Number field of the filtered group. A marked
    reference reads the captured outer row, not the level the filter reopens. -/
private def SurfaceCorrelatedHaving.readsGroupNumber (model : FlatModel) (declaringGroup : GroupPath)
    (group : RepeatableGroupDecl) : SurfaceCorrelatedHaving → Bool
  | .numeric _ left right =>
      (left.atoms ++ right.atoms).any fun
        | .field reference => reference.origin == .inner &&
            (model.resolveNumberInGroup declaringGroup group reference.field).isOk
        | .repetition _ => false
  | .and left right | .or left right =>
      left.readsGroupNumber model declaringGroup group ||
        right.readsGroupNumber model declaringGroup group
  | .compareStrings _ _ _ | .presence _ _ => false

/-- Elaborate the single-group route's body in two passes. The first reads and compares the whole
    body in authored order, so each leaf's reads and comparison class answer as it closes; the
    second asks the route's placement requirement, as the star route asks its candidate environment
    only after the whole body
    ([`spec/07`](../../spec/07-repetition-and-iteration.md),
    [checkpoint](../../docs/sources/static-admission-and-class-probes.md#src-field-value-read-grid)).
    A String leaf, which this route does not represent, still asks its read's gates first. A leaf
    outside the group draws the missing-iteration class only when no leaf reads one of the group's
    Number fields; beside such a leaf the Kernel admits it as a constant
    ([checkpoint](../../docs/sources/static-admission-and-class-probes.md#src-field-value-read-predictions)). -/
private def elaborateHavingCore (model : FlatModel) (declaringGroup : GroupPath)
    (group : RepeatableGroupDecl) (authored : SurfaceCorrelatedHaving) :
    Except CorrelationElabError CorrelatedHaving := do
  discard <| elaborateHavingCoreWith {
    number := model.resolveHavingNumberRead declaringGroup
    repetition := resolveHavingRepetitionInGroup declaringGroup group
    string := fun _ reference _ => do
      discard <| (checkFieldValueRead (model.resolveFieldDeclarationUnchecked declaringGroup reference.field)
        (model.havingGroupRead declaringGroup reference.field)).mapError .resolve
      throw .stringLeafOutsideStarRoute
    presence := fun _ _ => throw .stringLeafOutsideStarRoute } authored
  let readsGroup := authored.readsGroupNumber model declaringGroup group
  let condition ← (elaborateHavingCoreWith {
    number := model.resolveHavingNumberInGroup declaringGroup group
    repetition := resolveHavingRepetitionInGroup declaringGroup group
    -- The legacy one-group route admits neither newer leaf; both fail closed here.
    string := fun _ _ _ => throw .stringLeafOutsideStarRoute
    presence := fun _ _ => throw .stringLeafOutsideStarRoute } authored).mapError fun
      | .fieldOutsideGroup origin fieldPath expectedGroup =>
          if readsGroup then .constantLeafBesideIteratedLeaf origin fieldPath expectedGroup
          else .fieldOutsideGroup origin fieldPath expectedGroup
      | error => error
  -- Disjunction is refused here too: this route's well-formedness predicate requires a conjunctive
  -- core, and refusing at this arm names that cause instead of failing later as an unexplained
  -- incoherence.
  if condition.isConjunctive then
    pure condition
  else
    throw .disjunctionOutsideStarRoute

/-- A marked reference's level must lie in the captured environment, asked as the reference is
    resolved. An unmarked one's candidate environment is asked only after the whole body,
    `SurfaceCorrelatedHaving.candidateEnvironmentRefusal?`. -/
private def requireOuterFieldAvailable (origin : HavingOrigin) (outerLevels : List RepeatableLevel)
    (declaration : FlatFieldDecl) : Except CorrelationElabError Unit :=
  if origin == .outer && !repeatableScopeAvailable declaration.repeatableScope outerLevels then
    throw (.fieldOutsideEnvironment origin declaration.path outerLevels declaration.repeatableScope)
  else
    pure ()

/-- A filter body's field-value read, with the gates its bracket asks as it closes. A path naming a
    group draws the group class, measured on the level the filter iterates, on a fixed group
    ([checkpoint](../../docs/sources/static-admission-and-class-probes.md#src-field-value-read-grid))
    and on a repeatable group the filter does not iterate
    ([inbound](../../docs/SOURCES.md#inbound-2026-09-25g-field-value-read)). The value gates are asked
    on the same production's account; no row reads a raw String or a partial Date in a body. A marked reference's captured
    environment is asked before the value gates and the leaf's kind gate on the assumption that it
    is the reader's class, as an unstarred repeatable level is; no row pairs it with either. -/
private def FlatModel.resolveHavingFieldValueRead (model : FlatModel) (declaringGroup : GroupPath)
    (outerLevels : List RepeatableLevel) (origin : HavingOrigin) (reference : SurfaceFieldPath)
    (projectionRef : EnumerationProjectionRef := .stored) :
    Except CorrelationElabError FlatFieldDecl := do
  let declaration ← (displaceGroupRead (model.resolveFieldDeclarationUnchecked declaringGroup reference)
    (model.havingGroupRead declaringGroup reference)).mapError .resolve
  requireOuterFieldAvailable origin outerLevels declaration
  match declaration.projectedReadRefusal? projectionRef with
  | some refusal => throw (.resolve refusal)
  | none => pure declaration

private def FlatModel.resolveHavingNumberInEnvironment (model : FlatModel)
    (declaringGroup : GroupPath) (outerLevels : List RepeatableLevel)
    (origin : HavingOrigin) (reference : SurfaceFieldPath) :
    Except CorrelationElabError ResolvedNumberRef := do
  let declaration ← model.resolveHavingFieldValueRead declaringGroup outerLevels origin reference
  let field ← match declaration.toNumberField? with
    | some field => pure field
    | none =>
        throw (.fieldNotNumber declaration.path
          declaration.policy.kind.surfaceKind)
  pure { declaration, core := { origin, field } }

/-- Resolve text in its selected environment, retaining the ordinary comparison's model-owned
    projection and literal-domain checks rather than treating a category as a stored token. -/
private def FlatModel.resolveHavingStringInEnvironment (model : FlatModel)
    (declaringGroup : GroupPath) (outerLevels : List RepeatableLevel)
    (op : EqualityOp) (reference : SurfaceHavingStringRef) (expected : String) :
    Except CorrelationElabError HavingStringRef := do
  let declaration ← model.resolveHavingFieldValueRead declaringGroup outerLevels reference.origin
    reference.field reference.projectionRef
  let operand ← match declaration.policy.kind with
    | .enumeration => do
        let surfaceOp := match op with | .equal => SurfaceComparisonOp.equal | .notEqual => .notEqual
        let .compare (.enumeration _ operand _) ←
          (elaborateEnumerationCore declaration surfaceOp reference.projectionRef expected).mapError .text
          | throw .incoherentCore
        pure (.enumeration operand)
    | _ =>
        match declaration.toStringValueField?, reference.projectionRef with
        | some field, .stored => pure (.string field)
        | _, _ => throw (.fieldNotStringValue declaration.path declaration.policy.kind.surfaceKind)
  pure { origin := reference.origin, operand }

/-- Resolve one presence filter reference. Presence accepts any declared field, so this checks the
    declaration's existence and a marked one's captured environment, with no kind gate. -/
private def FlatModel.resolveHavingPresenceInEnvironment (model : FlatModel)
    (declaringGroup : GroupPath) (outerLevels : List RepeatableLevel)
    (origin : HavingOrigin) (reference : SurfaceFieldPath) :
    Except CorrelationElabError HavingPresenceRef := do
  let declaration ←
    (model.resolveFieldDeclarationUnchecked declaringGroup reference).mapError .resolve
  requireOuterFieldAvailable origin outerLevels declaration
  pure { origin, field := declaration.id }

private def FlatModel.resolveHavingRepetitionInEnvironment (model : FlatModel)
    (declaringGroup : GroupPath) (outerLevels : List RepeatableLevel)
    (origin : HavingOrigin) (reference : SurfaceGroupReference) :
    Except CorrelationElabError HavingRepetitionRef := do
  let resolved ← reference.resolveAgainst declaringGroup |>.mapError (.ofSingleGroup origin)
  if !model.hasGroupPath resolved.path then
    throw (.unknownRepetitionGroup resolved.path)
  if origin == .outer then
    let scope := model.repeatableScopeForGroupPath resolved.path
    if let some missing := scope.find? fun level => !outerLevels.contains level then
      throw (.repetitionOutsideEnvironment origin resolved.path outerLevels missing)
  let source := match model.repeatableGroups.find? (fun group => group.path == resolved.path) with
    | some group => HavingRepetitionSource.repeatable group.level
    | none => .fixed resolved.path
  pure { origin, source }

/-- An outer filter reference contributes its declaration's scope whatever the reference's kind, so
    this reads the origin and the field id rather than a kind-specific reference type. -/
private def outerHavingFieldIterationScope
    (model : FlatModel) (origin : HavingOrigin) (fieldId : FieldId) :
    Option (List RepeatableLevel) :=
  match origin with
  | .inner => none
  | .outer =>
      match model.lookupUniqueId fieldId with
      | .error _ => none
      | .ok declaration =>
          if declaration.repeatableScope.isEmpty then
            none
          else
            some declaration.repeatableScope

private def outerHavingNumberIterationScope
    (model : FlatModel) (reference : HavingNumberRef) :
    Option (List RepeatableLevel) :=
  outerHavingFieldIterationScope model reference.origin reference.field.id

private def outerHavingRepetitionIterationScope
    (model : FlatModel)
    (reference : HavingRepetitionRef) :
    Option (List RepeatableLevel) :=
  match reference.origin with
  | .inner => none
  | .outer => (reference.scope? model).bind fun scope =>
      if scope.isEmpty then none else some scope

def CorrelatedHaving.outerIterationScopes
    (model : FlatModel) :
    CorrelatedHaving → List (Option (List RepeatableLevel))
  | .leaf (.numeric comparison) =>
      (comparison.left.atoms ++ comparison.right.atoms).map fun
        | .field reference => outerHavingNumberIterationScope model reference
        | .repetition reference => outerHavingRepetitionIterationScope model reference
  | .leaf (.compareStringLiteral _ reference _) =>
      [outerHavingFieldIterationScope model reference.origin reference.field.id]
  | .leaf (.presence _ reference) =>
      [outerHavingFieldIterationScope model reference.origin reference.field]
  | .and left right | .or left right =>
      CorrelatedHaving.outerIterationScopes model left ++
        CorrelatedHaving.outerIterationScopes model right

/-- One filter certified against the candidate path and captured binding group. Lexical resolution
uses the separate declaring group passed to `elaborateStarHavingCore`. -/
structure CheckedStarHaving (model : FlatModel)
    (source : CheckedStarFieldPath model) (bindingGroup : GroupPath) where
  authored : CorrelatedHaving
  wellFormed : authored.wellFormedForEnvironments model
    (source.path.axes.map (·.level))
    (model.repeatableScopeForGroupPath bindingGroup) = true
  reachesReopenedLevel : authored.reachesReopenedLevel model
    ((source.path.axes.map (·.level)).drop source.path.firstStar) = true

def CheckedStarHaving.condition
    (checked : CheckedStarHaving model source declaringGroup) :
    CorrelatedHaving :=
  checked.authored

/-- The first **unmarked** reference of an authored filter, in authored order, whose level its
    candidate environment does not hold. The star route asks it once every leaf has resolved and
    passed its comparison's kind and scale gates, because the Kernel names a body's refused
    comparison ahead of the filter's iteration class, on a repetition the filter does not iterate
    too ([inbound](../../docs/SOURCES.md#inbound-2026-09-25c-filter-body)). -/
def SurfaceCorrelatedHaving.candidateEnvironmentRefusal? (model : FlatModel)
    (declaringGroup : GroupPath) (candidateLevels : List RepeatableLevel) :
    SurfaceCorrelatedHaving → Option CorrelationElabError
  | .numeric _ left right =>
      (left.atoms ++ right.atoms).findSome? fun
        | .field reference => field reference.origin reference.field
        | .repetition reference => group reference.origin reference.group
  | .compareStrings _ reference _ => field reference.origin reference.field
  | .presence _ reference => field reference.origin reference.field
  | .and left right | .or left right =>
      (left.candidateEnvironmentRefusal? model declaringGroup candidateLevels).orElse fun _ =>
        right.candidateEnvironmentRefusal? model declaringGroup candidateLevels
where
  field (origin : HavingOrigin) (reference : SurfaceFieldPath) : Option CorrelationElabError := do
    guard (origin == .inner)
    let declaration ← (model.resolveFieldDeclarationUnchecked declaringGroup reference).toOption
    guard !(repeatableScopeAvailable declaration.repeatableScope candidateLevels)
    pure (.fieldOutsideEnvironment .inner declaration.path candidateLevels
      declaration.repeatableScope)
  group (origin : HavingOrigin) (reference : SurfaceGroupReference) :
      Option CorrelationElabError := do
    guard (origin == .inner)
    let resolved ← (reference.resolveAgainst declaringGroup).toOption
    let missing ← (model.repeatableScopeForGroupPath resolved.path).find? fun level =>
      !candidateLevels.contains level
    pure (.repetitionOutsideEnvironment .inner resolved.path candidateLevels missing)

/-- Lower the supported numeric-expression, String and presence filter tree against one validated star plan. The result retains the authored connectives and exact candidate/captured environment split established by the checked references. -/
def elaborateStarHavingCore (model : FlatModel) (declaringGroup : GroupPath)
    (source : CheckedStarFieldPath model) (authored : SurfaceCorrelatedHaving)
    (bindingGroup : GroupPath := declaringGroup) :
    Except CorrelationElabError (CheckedStarHaving model source bindingGroup) := do
  let candidateLevels := source.path.axes.map (·.level)
  let reopenedLevels := candidateLevels.drop source.path.firstStar
  let outerLevels := model.repeatableScopeForGroupPath bindingGroup
  let condition ← elaborateHavingCoreWith {
    number := model.resolveHavingNumberInEnvironment declaringGroup outerLevels
    repetition := model.resolveHavingRepetitionInEnvironment declaringGroup outerLevels
    string := model.resolveHavingStringInEnvironment declaringGroup outerLevels
    presence := model.resolveHavingPresenceInEnvironment declaringGroup outerLevels } authored
  if let some refusal := authored.candidateEnvironmentRefusal? model declaringGroup candidateLevels then
    throw refusal
  if hReopened : condition.reachesReopenedLevel model reopenedLevels = true then
    if hWellFormed :
        condition.wellFormedForEnvironments model candidateLevels outerLevels = true then
      pure {
        authored := condition
        wellFormed := hWellFormed
        reachesReopenedLevel := hReopened }
    else
      throw .incoherentCore
  else
    throw .missingInner

namespace CheckedStarFieldPath

/-- Apply one checked validation `Having` to topology-produced leaves before invoking the kind-specific cell classifier. Every filtered star consumer shares this order and the retained filter marker. -/
def selectedValidationHavingValueListSide (_checked : CheckedStarFieldPath model)
    (resolved : ResolvedStarTopology) (having : CorrelatedHaving)
    (filterRead : Env → FieldId → CheckedCell) (outer : Env)
    (classify : Env → ValueListCell kind) : ResolvedValueListSide kind :=
  let filterContext : CorrelationContext := { read := filterRead }
  let selected := having.selectEnvironments filterContext outer resolved.environments
  { cells := selected.map classify
    hasUninstantiatedTail := resolved.domain.hasOpenTail
    hasHaving := true }

/-- Resolve nested topology once, filter every candidate against its complete candidate/captured environments, and classify only retained leaves. -/
def resolvedValidationHavingValueListSide (checked : CheckedStarFieldPath model)
    (document : Document) (outer : Env) (having : CorrelatedHaving)
    (filterRead : Env → FieldId → CheckedCell)
    (classify : Env → ValueListCell kind) :
    Except StarAddressingError (ResolvedValueListSide kind) := do
  let resolved ← checked.path.resolveInCapacity document outer
  pure (checked.selectedValidationHavingValueListSide resolved having filterRead outer classify)

/-- Dispatch one optional checked validation filter without duplicating the filter-before-classification branch in each scalar-kind adapter. -/
def resolvedOptionalValidationHavingValueListSide
    (checked : CheckedStarFieldPath model) (document : Document) (outer : Env)
    (filter : Option (CheckedStarHaving model checked declaringGroup))
    (filterRead : Env → FieldId → CheckedCell)
    (classify : Env → ValueListCell kind) :
    Except StarAddressingError (ResolvedValueListSide kind) :=
  match filter with
  | none => checked.resolvedValueListSide document outer classify
  | some having =>
      checked.resolvedValidationHavingValueListSide document outer
        having.condition filterRead classify

end CheckedStarFieldPath

/-- Partial validation skips a complete rule containing `Having` before topology or operand reads; otherwise it returns the evaluated value-list verdict. -/
inductive PartialHavingValueListResult where
  | skippedHaving
  | evaluated (verdict : Verdict)
  deriving Repr, DecidableEq

structure ResolvedSingleCorrelatedRule where
  group : RepeatableGroupDecl
  errorField : FlatNumberField
  guardField : FlatNumberField
  star : SingleCorrelatedStar

def ResolvedSingleCorrelatedRule.wellFormedBool
    (rule : ResolvedSingleCorrelatedRule) (model : FlatModel) : Bool :=
  model.repeatableGroups.contains rule.group &&
    model.admitsSingleGroupNumber rule.group rule.errorField &&
    model.admitsSingleGroupNumber rule.group rule.guardField &&
    rule.errorField == rule.guardField &&
    model.admitsSingleGroupNumber rule.group rule.star.valueField &&
    rule.star.having.condition.isConjunctive &&
    rule.star.having.condition.wellFormedForSingleGroup model rule.group

def ResolvedSingleCorrelatedRule.WellFormed
    (rule : ResolvedSingleCorrelatedRule) (model : FlatModel) : Prop :=
  rule.wellFormedBool model = true

/-- The only repeatable surface-to-core result accepted by the checked runtime route. -/
structure CheckedSingleCorrelatedRule (model : FlatModel) where
  core : ResolvedSingleCorrelatedRule
  modelWellFormed : model.validate.isOk = true
  wellFormed : core.WellFormed model

/-- Checked lowering for the exact one-star correlated validation fragment. All-inner `Having` is rejected as a routing boundary to the earlier uncorrelated capsule; it is not classified as kernel-invalid here. -/
def elaborateSingleCorrelatedRule (model : FlatModel) (declaringGroup : GroupPath)
    (rule : SurfaceSingleCorrelatedRule) :
    Except CorrelationElabError (CheckedSingleCorrelatedRule model) :=
  match hModel : model.validate with
  | .error error => .error (.resolve error)
  | .ok () => do
      let groupReference ← rule.valueField.groupReference |>.mapError (.ofSingleGroup .inner)
      let groupPath ← groupReference.resolveAgainst declaringGroup |>.mapError (.ofSingleGroup .inner)
      let group ← (model.lookupUniqueRepeatablePath groupPath).mapError .resolve
      let valueReference : SurfaceFieldPath :=
        { base := .absolute, groups := group.path, field := rule.valueField.field }
      let (_, valueField) ←
        model.resolveNumberInGroup declaringGroup group valueReference |>.mapError (.ofSingleGroup .inner)
      let (errorDeclaration, errorField) ←
        model.resolveNumberInGroup declaringGroup group rule.errorField |>.mapError (.ofSingleGroup .inner)
      let (guardDeclaration, guardField) ←
        model.resolveNumberInGroup declaringGroup group rule.guardField |>.mapError (.ofSingleGroup .inner)
      if errorField != guardField then
        throw (.errorGuardMismatch errorDeclaration.path guardDeclaration.path)
      let condition ← elaborateHavingCore model declaringGroup group rule.having
      let having ← match condition.check with
        | .ok checked => pure checked
        | .error .missingInner => throw .missingInner
        | .error .missingOuter => throw .missingOuter
      let core : ResolvedSingleCorrelatedRule :=
        { group, errorField, guardField, star := { valueField, having } }
      if hCore : core.wellFormedBool model = true then
        pure {
          core
          modelWellFormed := by
            rw [hModel]
            rfl
          wellFormed := hCore
        }
      else
        throw .incoherentCore

def CheckedSingleCorrelatedRule.firingRows
    (checked : CheckedSingleCorrelatedRule model) (raw : RawSingleGroupContext) :
    Except SingleGroupContextError (List RowIndex) := do
  raw.validate
  pure <| checked.core.star.firingRowsOn checked.core.guardField
    (model.checkSingleGroupContext checked.core.group raw)

end A12Kernel
