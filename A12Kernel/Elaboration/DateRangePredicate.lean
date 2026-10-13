import A12Kernel.Elaboration.IteratedDateRangeCondition
import A12Kernel.Elaboration.ScalarFieldComparison

namespace A12Kernel

inductive SurfaceDateRangeComparison where
  | stored (left right : SurfaceFieldPath)
  | mixed (start finish : SurfaceDateRangeEndpoint) (stored : SurfaceFieldPath) (position : DateRangeConstructionPosition)
  | constructed (leftStart leftFinish rightStart rightFinish : SurfaceDateRangeEndpoint)

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
def evalComputation (source : CheckedDateRangePredicate model) (context : ScalarComputationContext) :
    Except FieldId ComputationConditionResult :=
  let constructed (source : CheckedDateRangeConstruction model) := do
    let observation ← source.evaluateInContext .computation context
      |>.mapError (fun
        | .endpointValueKind field | .endpointDateUnavailable field _ => field
        | .document _ | .addressing _ => source.start.checked.target.id)
    pure observation.comparisonOperand
  let stored (source : CheckedDateRangeSource model) :=
    (CheckedDateRangeSource.observeRange source.declaration.id .computation (context.read source.declaration.id))
      |>.mapError (fun _ => source.declaration.id) |>.map CellObservation.asValidationSimpleOperand
  match source with
  | .stored source => (CheckedScalarFieldComparison.range source).evalComputation { read := context.read, storedText := context.storedText, world := context.world }
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
def elaborateDateRangePredicate (model : FlatModel) (group : GroupPath) (scope : List RepeatableLevel)
    (entityRead valueRead : SurfaceFieldPath → Except ResolveError FlatFieldDecl)
    (operator : EqualityOp) (source : SurfaceDateRangeComparison) :
    Except DateRangePredicateElabError (CheckedDateRangePredicate model) := do
  let value := fun path => (valueRead path).mapError DateRangePredicateElabError.read
  let endpoint (source : SurfaceDateRangeEndpoint) : Except DateRangeEndpointElabError (CheckedDateRangeEndpoint model) := do
    match source with
    | .field path =>
        let declaration ← (entityRead path).mapError (DateRangeEndpointElabError.targetPolicy ∘ TemporalTargetElabError.resolve)
        elaborateDateRangeEndpointIn model scope declaration.id
    | .indexed _ => elaborateDateRangeEndpointSource model group scope source
  let construction (start finish : SurfaceDateRangeEndpoint) : Except DateRangeConstructionElabError (CheckedDateRangeConstruction model) := do
    checkDateRangeConstructionEndpoints (← (endpoint start).mapError .start) (← (endpoint finish).mapError .finish)
  match source with
  | .stored left right =>
      let left ← value left
      let right ← value right
      .stored <$> (elaborateDateRangeSourceComparisonIn model scope left.id right.id operator).mapError
        (DateRangePredicateElabError.condition ∘ IteratedDateRangeConditionElabError.storedEquality)
  | .constructed leftStart leftFinish rightStart rightFinish =>
      let checked : Except DateRangeConstructionComparisonElabError (CheckedDateRangeConstructionComparison model) := do
        let left ← (construction leftStart leftFinish).mapError .left
        let right ← (construction rightStart rightFinish).mapError .right
        if same : left.start.format.sameComponents right.start.format then
          pure { left, right, comparison := operator, componentsMatch := same }
        else throw (.componentMismatch left.start.format right.start.format)
      .constructed <$> checked.mapError
        (DateRangePredicateElabError.condition ∘ IteratedDateRangeConditionElabError.constructionPair)
  | .mixed start finish stored position =>
      let storedFirst ← if position == .right then some <$> value stored else pure none
      let construction ← (construction start finish).mapError
        (DateRangePredicateElabError.condition ∘ IteratedDateRangeConditionElabError.construction)
      let stored ← match storedFirst with | some declaration => pure declaration | none => value stored
      .mixed <$> (checkConstructionStoredComparisonIn model scope construction stored.id position operator).mapError
        DateRangePredicateElabError.condition

end A12Kernel
