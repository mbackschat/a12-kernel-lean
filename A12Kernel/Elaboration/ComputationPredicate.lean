import A12Kernel.Elaboration.ValueListCondition
import A12Kernel.Elaboration.NumericAggregate.Entities
import A12Kernel.Semantics.ComputationValueList

namespace A12Kernel

inductive SurfaceComputationPredicate where
  | entityValueList (source : SurfaceNumberEntityValueListSource)
  | tokenLiteralValueList (source : SurfaceTokenEntityStringLiteralValueListSource)
  deriving Repr, DecidableEq

inductive ComputationPredicateElabError where
  | token (error : TokenEntityValueListElabError)
  | literals (error : TokenEntityStringLiteralValueListElabError)
  | filteredSource
  deriving Repr, DecidableEq

inductive ComputationPredicateError where
  | contextRequired
  | filteredSource
  | addressing (error : StarAddressingError)
  deriving Repr, DecidableEq

/-- Retain the existing typed source certificate instead of erasing membership into a validation
verdict. Filtered sources need a continuation-aware reader and are excluded by admission. -/
inductive CheckedComputationPredicate (model : FlatModel) where
  | valueList (source : CheckedValueListCondition model)

namespace CheckedComputationPredicate

def referencesField (predicate : CheckedComputationPredicate model) (field : FieldId) : Bool :=
  match predicate with
  | .valueList source => source.referencesField field

def rowBoundBool (predicate : CheckedComputationPredicate model) (scope : List RepeatableLevel) : Bool :=
  match predicate with
  | .valueList source => !source.hasHaving && source.bindingScopes.all (·.isPrefixOf scope)

private def addressed (context : ScalarComputationContext) : Except ComputationPredicateError ComputationFillContext :=
  match context.addressed with
  | some addressed => pure addressed
  | none => throw .contextRequired

private def resolveNumber (context : ScalarComputationContext) :
    CheckedNumberEntityOperand model → Except ComputationPredicateError (ResolvedValueListSide .number)
  | .field source => pure (source.resolvedAggregateSideAt .computation { read := context.read })
  | .star source => do
      let addressed ← addressed context
      let resolved ← (source.source.path.resolveInCapacity addressed.document context.row).mapError .addressing
      pure (resolved.toResolvedSide (source.checkedValueListCellAt .computation addressed.read))
  | .group source => do
      let addressed ← addressed context
      (source.resolvedSideIn .computation addressed.document context.row addressed.read).mapError .addressing
  | .starHaving _ => throw .filteredSource

private def resolveToken (context : ScalarComputationContext) :
    CheckedTokenEntityOperand model → Except ComputationPredicateError (ResolvedValueListSide .token)
  | .field source => pure (source.resolvedSideAt .computation context.read)
  | .star source => do
      let addressed ← addressed context
      if source.filter.isSome then throw .filteredSource
      let resolved ← (source.source.path.resolveInCapacity addressed.document context.row).mapError .addressing
      pure (resolved.toResolvedSide (source.valueListCellAt .computation addressed.read))
  | .group source => do
      let addressed ← addressed context
      (source.resolvedSideIn .computation addressed.document context.row addressed.read).mapError .addressing

def evalChecked (predicate : CheckedComputationPredicate model)
    (context : ScalarComputationContext) : Except ComputationPredicateError ComputationConditionResult := do
  match predicate with
  | .valueList (.number source) =>
      source.quantifier.evalComputationWith (resolveNumber context) (resolveNumber context)
        source.fields.operands source.values.operands
  | .valueList (.token source) =>
      source.quantifier.evalComputationWith (resolveToken context) (resolveToken context)
        source.fields.operands source.values.operands
  | .valueList (.literals source) =>
      source.quantifier.evalComputationWith (resolveToken context)
        (fun value => pure ({ cells := [.present value], hasUninstantiatedTail := false, hasHaving := false } :
          ResolvedValueListSide .token)) source.fields.operands (source.firstValue :: source.restValues)

end CheckedComputationPredicate

def FlatModel.elaborateComputationPredicate (model : FlatModel)
    (declaringGroup targetGroup : GroupPath) (surface : SurfaceComputationPredicate) :
    Except ComputationPredicateElabError (CheckedComputationPredicate model) := do
  let checked ← match surface with
    | .entityValueList source =>
        match elaborateNumberEntityValueListSource model declaringGroup source (some targetGroup) with
        | .ok checked => pure (CheckedValueListCondition.number checked)
        | .error _ =>
            CheckedValueListCondition.token <$>
              (elaborateTokenEntityValueListSource model declaringGroup
                { quantifier := source.quantifier, fields := source.fields, values := source.values }
                (targetGroup? := some targetGroup)).mapError .token
    | .tokenLiteralValueList source =>
        CheckedValueListCondition.literals <$>
          (elaborateTokenEntityStringLiteralValueListSource model declaringGroup source
            (targetGroup? := some targetGroup)).mapError .literals
  if checked.hasHaving then throw .filteredSource
  pure (.valueList checked)

end A12Kernel
