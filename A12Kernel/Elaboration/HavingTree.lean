import A12Kernel.Elaboration.HavingNumericAtom
import A12Kernel.Elaboration.CorrelationSurface
import A12Kernel.Elaboration.CorrelationWellFormed
import A12Kernel.Elaboration.LiteralComparisonDiagnostic

/-! Route-independent filter-tree elaboration. Legacy and checked-star routes supply their own reference resolvers so shared connective and numeric admission stay identical. -/

namespace A12Kernel

private def SurfaceComparisonOp.toCorrelation : SurfaceComparisonOp → CorrelationComparisonOp
  | .equal => .equal
  | .notEqual => .notEqual
  | .less => .lessThan
  | .lessEqual => .lessEqual
  | .greater => .greaterThan
  | .greaterEqual => .greaterEqual

/-- The per-leaf reference resolvers one filter route supplies. They travel as a bundle because
    each route chooses all of them together, and a route that admits no String or presence leaf
    supplies a refusing resolver rather than a different combinator. -/
structure HavingLeafResolvers extends HavingNumericResolvers where
  stringExpression : SurfaceComparisonOp → StringExpr SurfaceHavingSelectedOperand String → StringExpr SurfaceHavingSelectedOperand String →
    Except CorrelationElabError HavingStringComparison
  selectedComparison : EqualityOp → SurfaceHavingSelectedOperand → SurfaceHavingSelectedOperand →
    Except CorrelationElabError HavingSelectedComparison
  boolean : SurfaceComparisonOp → SurfaceHavingStringRef → Bool → Except CorrelationElabError FlatComparison
  fields : SurfaceComparisonOp → SurfaceHavingStringRef → SurfaceHavingStringRef →
    Except CorrelationElabError (Option FlatComparison)

  temporalExpression : SurfaceComparisonOp → SurfaceHavingTemporalExpression → SurfaceHavingTemporalExpression →
    Except CorrelationElabError HavingTemporalComparison
  temporalDifference : TemporalOperationUnit → SurfaceHavingTemporalExpression → SurfaceHavingTemporalExpression → Except CorrelationElabError HavingNumericAtom
  temporalExpressionPart : TemporalNumericPart → SurfaceHavingTemporalExpression → Except CorrelationElabError HavingNumericAtom
  temporal : SurfaceComparisonOp → SurfaceHavingTemporalOperand → SurfaceHavingTemporalOperand →
    Except CorrelationElabError (Option (HavingOrigin × HavingOrigin × FlatComparison))
  string : SurfaceComparisonOp → SurfaceHavingStringRef → String →
    Except CorrelationElabError (EqualityOp × HavingStringRef)
  literalMembership : SurfaceHavingStringRef → Sum (List Int) (List String) →
    Except CorrelationElabError FlatLiteralMembership
  literalList : SurfaceHavingEntitySource → List String → Except CorrelationElabError HavingFieldValueList
  dateValidity : SurfaceHavingDateComponents → Except CorrelationElabError HavingConstructedDate
  dateRange : SurfaceHavingDateRangePredicate → Except CorrelationElabError HavingDateRangePredicate := fun _ => throw .stringLeafOutsideStarRoute
  uniqueness : SurfaceHavingEntitySource → Except CorrelationElabError HavingUniqueness
  fieldMembership : ComputationValueListOperator → SurfaceHavingEntitySource → SurfaceHavingEntitySource →
    Except CorrelationElabError HavingFieldValueList
  fieldFill : SurfaceHavingEntitySource → Except CorrelationElabError (List (HavingFieldListSlot HavingPresenceRef))
  groupPresence : HavingOrigin → SurfaceGroupReference → Except CorrelationElabError ComputationGroupOperand
  groupFill : GroupFillQuantifier → SurfaceHavingEntityOperand →
    List SurfaceHavingEntityOperand → Except CorrelationElabError (HavingGroupOperand × List HavingGroupOperand)
  stringPattern : HavingOrigin → SurfaceFieldPath → String →
    Except CorrelationElabError (HavingPresenceRef × CompiledStringPattern)
  typeValidity : HavingOrigin → SurfaceFieldPath → String → Except CorrelationElabError HavingPresenceRef
  presence : HavingOrigin → SurfaceFieldPath →
    Except CorrelationElabError HavingPresenceRef

/-- Both sides of an ordering comparison, a kind refusal carrying its partner's kind. A side whose
    read fails answers ahead of both kind gates, the left one first, so a left kind refusal meeting a
    right read failure raises the right's error. -/
private def orderingSides (left right : Except CorrelationElabError ResolvedHavingNumberRef) :
    Except CorrelationElabError (ResolvedHavingNumberRef × ResolvedHavingNumberRef) :=
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

private def elaborateHavingNumericExpression (resolvers : HavingLeafResolvers)
    (op : NumericValidationOp) (left right : AuthoredNumericExpr SurfaceHavingNumericAtom) :
    Except CorrelationElabError CorrelatedHaving := do
  let resolve := fun atom => resolvers.toHavingNumericResolvers.resolveWith atom
    (fun unit left right _ _ => resolvers.temporalDifference unit left right)
    (fun part source _ => resolvers.temporalExpressionPart part source)
  let leftCore ← left.mapM resolve
  let rightCore ← right.mapM resolve
  if leftCore.isImmediateLiteral && rightCore.isImmediateLiteral then
    throw .constantNumericComparison
  let comparison : NumericComparisonOf HavingNumericAtom :=
    { op := op, left := leftCore, right := rightCore }
  if !comparison.havingAdmitted (fun _ => true) then
    throw .numericExpressionUnsupported
  pure (.leaf (.numeric comparison))

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
  | _, _ => elaborateHavingNumericExpression resolvers (.ordinary op.toCorrelation.toNumeric) left right

def elaborateHavingCoreWith (resolvers : HavingLeafResolvers) :
    SurfaceCorrelatedHaving → Except CorrelationElabError CorrelatedHaving
  | .compareStringExpression op left right =>
      (fun comparison => .leaf (.stringExpression comparison)) <$> resolvers.stringExpression op left right
  | .compareSelected op left right =>
      (fun comparison => .leaf (.selectedComparison comparison)) <$> resolvers.selectedComparison op left right
  | .compareBoolean op reference expected => do
      pure (.leaf (.simpleComparison reference.origin .inner (← resolvers.boolean op reference expected)))
  | .compareTemporalExpression op left right => (fun comparison => .leaf (.temporalExpression comparison)) <$> resolvers.temporalExpression op left right
  | .compareTemporal op left right => do
      match ← resolvers.temporal op left right with
      | some (leftOrigin, rightOrigin, comparison) =>
          pure (.leaf (.simpleComparison leftOrigin rightOrigin comparison))
      | none =>
          let rec numeric : SurfaceHavingTemporalOperand → Except CorrelationElabError (AuthoredNumericExpr SurfaceHavingNumericAtom)
            | .field reference => pure (.atom (.field { origin := reference.origin, field := reference.field }))
            | .constant (.baseYear .direct) => pure (.atom .baseYear)
            | .grouped source => .group <$> numeric source
            | _ => throw .incoherentCore
          elaborateHavingNumeric resolvers op (← numeric left) (← numeric right)
  | .compareFields op left right => do
      match ← resolvers.fields op left right with
      | some comparison => pure (.leaf (.simpleComparison left.origin right.origin comparison))
      | none =>
          if left.projectionRef != .stored || right.projectionRef != .stored then
            throw .stringLeafOutsideStarRoute
          else
            elaborateHavingNumeric resolvers op
              (.atom (.field { origin := left.origin, field := left.field }))
              (.atom (.field { origin := right.origin, field := right.field }))
  | .numeric op left right => elaborateHavingNumeric resolvers op left right
  | .tolerance range left right => elaborateHavingNumericExpression resolvers (.tolerance range) left right
  | .compareStrings op reference expected => do
      let (equality, source) ← resolvers.string op reference expected
      pure (.compareStringLiteral equality source expected)
  | .literalMembership operator reference values => do
      pure (.leaf (.literalMembership reference.origin operator (← resolvers.literalMembership reference values)))
  | .literalList quantifier subjects values => do
      pure (.leaf (.fieldMembership (.quantified quantifier) (← resolvers.literalList subjects values)))
  | .dateValidity operation source => (.leaf ∘ CorrelatedHavingLeaf.dateValidity operation) <$> resolvers.dateValidity source
  | .dateRange source => (.leaf ∘ CorrelatedHavingLeaf.dateRange) <$> resolvers.dateRange source
  | .uniqueness source => (.leaf ∘ CorrelatedHavingLeaf.uniqueness) <$> resolvers.uniqueness source
  | .fieldMembership operator subjects members => do
      pure (.leaf (.fieldMembership operator (← resolvers.fieldMembership operator subjects members)))
  | .fieldFill operator source => do
      pure (.leaf (.fieldFill operator (← resolvers.fieldFill source)))
  | .presence polarity reference => do
      pure (.presence polarity
        (← resolvers.presence reference.origin reference.field))
  | .stringPattern operation reference source => do
      let (reference, compiled) ← resolvers.stringPattern reference.origin reference.field source
      pure (.leaf (.stringPattern operation reference compiled))
  | .typeValidity operation reference name => do
      pure (.leaf (.typeValidity operation (← resolvers.typeValidity reference.origin reference.field name) name))
  | .groupPresence operator origin reference => do
      pure (.leaf (.groupPresence operator origin (← resolvers.groupPresence origin reference)))
  | .groupFill operator first rest => do
      let (first, rest) ← resolvers.groupFill operator first rest
      pure (.leaf (.groupFill operator first rest))
  | .and left right => do
      pure (.and (← elaborateHavingCoreWith resolvers left)
        (← elaborateHavingCoreWith resolvers right))
  | .or left right => do
      pure (.or (← elaborateHavingCoreWith resolvers left)
        (← elaborateHavingCoreWith resolvers right))

end A12Kernel
