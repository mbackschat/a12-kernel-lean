import A12Kernel.Elaboration.IteratedDateRangeCondition
import A12Kernel.Elaboration.ScalarFieldComparison

namespace A12Kernel

inductive SurfaceDateRangeComparison where
  | stored (left right : SurfaceFieldPath)
  | mixed (start finish stored : SurfaceFieldPath) (position : DateRangeConstructionPosition)
  | constructed (leftStart leftFinish rightStart rightFinish : SurfaceFieldPath)

/-- Ordinary predicates retain the existing certificates for the three range-comparison shapes.
The validation bridge and computation guard therefore share component and scope admission. -/
inductive CheckedDateRangePredicate (model : FlatModel) where
  | stored (source : CheckedDateRangeSourceComparison model)
  | mixed (source : CheckedIteratedConstructionStoredComparison model)
  | constructed (source : CheckedDateRangeConstructionComparison model)

namespace CheckedDateRangePredicate

def toValidation : CheckedDateRangePredicate model → IteratedDateRangeCondition model
  | .stored source => .storedEquality source
  | .mixed source => .constructionAgainstStored source
  | .constructed source => .constructionAgainstConstruction source

def referencesField (source : CheckedDateRangePredicate model) (field : FieldId) : Bool :=
  source.toValidation.referencesField field

def rowBoundBool (source : CheckedDateRangePredicate model) (scope : List RepeatableLevel) : Bool :=
  source.toValidation.bindingScopes.all (·.isPrefixOf scope)

/-- Endpoint completion consumes current cells; comparison keeps empty suppression separate from
reached poison, using the same ordered fold as other guards (spec/05 §8; having-range-family). -/
def evalComputation (source : CheckedDateRangePredicate model) (context : FlatContext) :
    Except FieldId ComputationConditionResult :=
  let constructed (source : CheckedDateRangeConstruction model) := do
    let observation ← source.evaluateWith .computation (fun field => pure (context.read field))
      |>.mapError (fun
        | .endpointValueKind field | .endpointDateUnavailable field _ => field
        | .document _ => source.start.checked.target.id)
    pure observation.comparisonOperand
  let stored (source : CheckedDateRangeSource model) :=
    (CheckedDateRangeSource.observeRange source.declaration.id .computation (context.read source.declaration.id))
      |>.mapError (fun _ => source.declaration.id) |>.map CellObservation.asValidationSimpleOperand
  match source with
  | .stored source => (CheckedScalarFieldComparison.range source).evalComputation context
  | .mixed source =>
      let holds := fun left right => source.comparison.holds (left.sameIdentity right)
      match source.position with
      | .left => evalComputationComparisonExcept holds (constructed source.construction) (fun _ => stored source.stored)
      | .right => evalComputationComparisonExcept holds (stored source.stored) (fun _ => constructed source.construction)
  | .constructed source =>
      evalComputationComparisonExcept (fun left right => source.comparison.holds (left.sameIdentity right))
        (constructed source.left) (fun _ => constructed source.right)

end CheckedDateRangePredicate

inductive DateRangePredicateElabError where
  | read (error : ResolveError)
  | condition (error : IteratedDateRangeConditionElabError)
  deriving Repr, DecidableEq

/-- The caller supplies its existing entity/value-read gates; certified endpoint and comparison
admission then remain common to ordinary validation and computation (spec/05 §8). -/
def elaborateDateRangePredicate (model : FlatModel) (scope : List RepeatableLevel)
    (entityRead valueRead : SurfaceFieldPath → Except ResolveError FlatFieldDecl)
    (operator : EqualityOp) (source : SurfaceDateRangeComparison) :
    Except DateRangePredicateElabError (CheckedDateRangePredicate model) := do
  let entity := fun path => (entityRead path).mapError DateRangePredicateElabError.read
  let value := fun path => (valueRead path).mapError DateRangePredicateElabError.read
  match source with
  | .stored left right =>
      let left ← value left
      let right ← value right
      .stored <$> (elaborateDateRangeSourceComparisonIn model scope left.id right.id operator).mapError
        (DateRangePredicateElabError.condition ∘ IteratedDateRangeConditionElabError.storedEquality)
  | .constructed leftStart leftFinish rightStart rightFinish =>
      let leftStart ← entity leftStart
      let leftFinish ← entity leftFinish
      let rightStart ← entity rightStart
      let rightFinish ← entity rightFinish
      .constructed <$> (elaborateDateRangeConstructionComparisonIn model scope
        leftStart.id leftFinish.id rightStart.id rightFinish.id operator).mapError
        (DateRangePredicateElabError.condition ∘ IteratedDateRangeConditionElabError.constructionPair)
  | .mixed start finish stored position =>
      let storedFirst ← if position == .right then some <$> value stored else pure none
      let start ← entity start
      let finish ← entity finish
      let stored ← match storedFirst with | some declaration => pure declaration | none => value stored
      .mixed <$> (elaborateConstructionStoredComparisonIn model scope start.id finish.id stored.id position operator).mapError
        DateRangePredicateElabError.condition

end A12Kernel
