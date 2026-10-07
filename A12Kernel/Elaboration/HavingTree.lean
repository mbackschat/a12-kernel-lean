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

structure ResolvedHavingNumberRef where
  declaration : FlatFieldDecl
  core : HavingNumberRef

/-- The per-leaf reference resolvers one filter route supplies. They travel as a bundle because
    each route chooses all of them together, and a route that admits no String or presence leaf
    supplies a refusing resolver rather than a different combinator. -/
structure HavingLeafResolvers where
  aggregate : NumericAggregateOp → SurfaceHavingNumberRef → List SurfaceHavingNumberRef → Except CorrelationElabError HavingNumericAtom
  baseYear : Except CorrelationElabError Int
  clockPart : HavingClockSource → TemporalNumericPart → Except CorrelationElabError HavingNumericAtom
  fieldValueAsNumber : SurfaceHavingStringRef → Except CorrelationElabError ResolvedFieldValueAsNumberSource
  boolean : EqualityOp → SurfaceHavingStringRef → Bool → Except CorrelationElabError FlatComparison
  fields : SurfaceComparisonOp → SurfaceHavingStringRef → SurfaceHavingStringRef →
    Except CorrelationElabError (Option FlatComparison)

  temporal : SurfaceComparisonOp → SurfaceHavingTemporalOperand → SurfaceHavingTemporalOperand →
    Except CorrelationElabError (Option (HavingOrigin × HavingOrigin × FlatComparison))
  stringValue : HavingOrigin → SurfaceFieldPath → Except CorrelationElabError FlatStringField
  dateDifference : DateDifferenceUnit → SurfaceDateDifferenceOperand SurfaceHavingTemporalRef → SurfaceDateDifferenceOperand SurfaceHavingTemporalRef → Except CorrelationElabError HavingNumericAtom
  dayDifference : SurfaceDateDifferenceOperand SurfaceHavingTemporalRef → SurfaceDateDifferenceOperand SurfaceHavingTemporalRef → Except CorrelationElabError HavingNumericAtom
  dateTimeDifference : DateTimeSubdayUnit → SurfaceDateDifferenceOperand SurfaceHavingTemporalRef → SurfaceDateDifferenceOperand SurfaceHavingTemporalRef → Except CorrelationElabError HavingNumericAtom
  dateRangeBoundPart : HavingOrigin → SurfaceFieldPath → DateNumericPart → Except CorrelationElabError FlatDateRangeField
  temporalPart : HavingOrigin → SurfaceFieldPath → TemporalNumericPart → Except CorrelationElabError FlatTemporalField
  number : HavingOrigin → SurfaceFieldPath →
    Except CorrelationElabError ResolvedHavingNumberRef
  repetition : HavingOrigin → SurfaceGroupReference →
    Except CorrelationElabError HavingRepetitionRef
  string : EqualityOp → SurfaceHavingStringRef → String →
    Except CorrelationElabError HavingStringRef
  literalMembership : SurfaceHavingStringRef → Sum (List Int) (List String) →
    Except CorrelationElabError FlatLiteralMembership
  literalList : SurfaceHavingDirectFieldSource → List String → Except CorrelationElabError HavingFieldValueList
  dateValidity : SurfaceHavingDateComponents → Except CorrelationElabError HavingDateComponents
  uniqueness : SurfaceHavingEntitySource → Except CorrelationElabError HavingUniqueness
  fieldMembership : ComputationValueListOperator → SurfaceHavingDirectFieldSource → SurfaceHavingDirectFieldSource →
    Except CorrelationElabError HavingFieldValueList
  fieldFill : SurfaceHavingDirectFieldSource → Except CorrelationElabError (List HavingPresenceRef)
  groupPresence : HavingOrigin → SurfaceGroupReference → Except CorrelationElabError ComputationGroupOperand
  groupFill : GroupFillQuantifier → (HavingOrigin × SurfaceGroupReference) →
    List (HavingOrigin × SurfaceGroupReference) → Except CorrelationElabError (HavingGroupOperand × List HavingGroupOperand)
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
  let resolve : SurfaceHavingNumericAtom → Except CorrelationElabError HavingNumericAtom
    | .aggregate op first rest => resolvers.aggregate op first rest
    | .dateDifference unit left right => resolvers.dateDifference unit left right
    | .dayDifference left right => resolvers.dayDifference left right
    | .dateTimeDifference unit left right => resolvers.dateTimeDifference unit left right
    | .baseYear => HavingNumericAtom.baseYear <$> resolvers.baseYear
    | .baseYearDatePart source part => (fun year => .baseYearDatePart year source part) <$> resolvers.baseYear
    | .clockPart source part => resolvers.clockPart source part
    | .fieldValueAsNumber reference => (.fieldValueAsNumber reference.origin ·) <$> resolvers.fieldValueAsNumber reference
    | .stringLength origin reference => (.stringLength origin ·) <$> resolvers.stringValue origin reference
    | .stringRange origin reference start finish => do
        let source ← (resolvers.stringValue origin reference).mapError fun
          | .text (.lengthOperandKindMismatch _ _) => .numericExpressionUnsupported
          | error => error
        if !validStringRange start finish then throw .numericExpressionUnsupported
        pure (.stringRange origin source start finish)
    | .dateRangeBoundPart origin reference bound part =>
        (fun source => .dateRangeBoundPart origin source bound part) <$> resolvers.dateRangeBoundPart origin reference part
    | .temporalPart origin reference part =>
        (fun source => .temporalPart origin source part) <$> resolvers.temporalPart origin reference part
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
  | .compareBoolean op reference expected => do
      pure (.leaf (.simpleComparison reference.origin .inner (← resolvers.boolean op reference expected)))
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
      pure (.compareStringLiteral op
        (← resolvers.string op reference expected) expected)
  | .literalMembership operator reference values => do
      pure (.leaf (.literalMembership reference.origin operator (← resolvers.literalMembership reference values)))
  | .literalList quantifier subjects values => do
      pure (.leaf (.fieldMembership (.quantified quantifier) (← resolvers.literalList subjects values)))
  | .dateValidity operation source => (.leaf ∘ CorrelatedHavingLeaf.dateValidity operation) <$> resolvers.dateValidity source
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
