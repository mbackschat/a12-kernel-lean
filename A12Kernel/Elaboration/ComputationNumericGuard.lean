import A12Kernel.Elaboration.NumericComputation.Evaluation
import A12Kernel.Elaboration.ComputationPredicate

namespace A12Kernel

/-- Computation guards retain the same model-certified numeric atoms as their operations. -/
abbrev CheckedComputationCondition (model : FlatModel) :=
  ComputationConditionOf (CheckedNumericComputationAtom model) (CheckedComputationPredicate model)

abbrev CheckedComputationAlternative (model : FlatModel) (Operation : Type) :=
  ComputationAlternative Operation (CheckedComputationCondition model)

inductive CheckedComputationConditionError where
  | primitive (error : ComputationConditionError)
  | numeric (error : NumericComputationFault)
  | predicate (error : ComputationPredicateError)
  deriving Repr, DecidableEq

def CheckedComputationConditionError.toNumericFault :
    CheckedComputationConditionError → NumericComputationFault
  | .predicate (.indexSelection error) => .indexSelection error
  | .primitive error => .guardBinding error
  | .numeric error => error
  | .predicate (.stringExpression error) => .stringExpression error
  | .predicate .valueFailure => .guardValueFailure
  | .predicate .temporalUnavailable => .unsupportedDateCalendar
  | .predicate (.fieldKindMismatch field) => .fieldKindMismatch field
  | .predicate (.fieldFill error) => .guardBinding (.fieldFill error)
  | .predicate .contextRequired => .repeatableContextRequired
  | .predicate (.addressing error) => .repeatableAddressing error

/-- Every target handler distinguishes a reached value failure from inherited operand poison;
the failure can originate in either a scalar predicate or a filtered numeric source (spec/09). -/
def CheckedComputationConditionError.isValueFailure (error : CheckedComputationConditionError) : Bool :=
  error.toNumericFault == .guardValueFailure || error.toNumericFault.isFilterValueFailure

inductive CheckedComputationConditionElabError where
  | primitive (error : ComputationConditionElabError)
  | numeric (error : NumericComputationElabError)
  | predicate (error : ComputationPredicateElabError)
  | incoherent
  deriving Repr, DecidableEq

namespace CheckedComputationCondition

abbrev fieldFilled (field : FieldId) : CheckedComputationCondition model := .leaf (.fieldFilled field)

abbrev fieldNotFilled (field : FieldId) : CheckedComputationCondition model := .leaf (.fieldNotFilled field)

abbrev and (left right : CheckedComputationCondition model) : CheckedComputationCondition model :=
  ConditionTree.and left right

abbrev or (left right : CheckedComputationCondition model) : CheckedComputationCondition model :=
  ConditionTree.or left right

def referencesField (condition : CheckedComputationCondition model) (field : FieldId) : Bool :=
  ComputationConditionOf.referencesFieldWith condition
    (fun atom field => atom.references model field) (·.referencesField) field

def forbidsTarget (condition : CheckedComputationCondition model) (field : FieldId) : Bool :=
  ComputationConditionOf.forbidsTargetWith condition
    (fun atom field => atom.forbidsTarget model field) (·.forbidsTarget) field

def requiresProducer (condition : CheckedComputationCondition model) (consumer producer : FieldId)
    (producerProtected : ResolvedGroupReference → Bool) : Bool :=
  ComputationConditionOf.requiresProducerWith condition
    (fun atom field => atom.requiresProducer model consumer field producerProtected)
    (fun predicate field => predicate.requiresProducer consumer field producerProtected) consumer producer producerProtected

def rowBoundBool (condition : CheckedComputationCondition model) (scope : List RepeatableLevel) : Bool :=
  condition.allLeaves fun
    | .predicate source => source.rowBoundBool scope
    | .numeric comparison => comparison.admittedWith (model.admitsNumericComputationOperand scope)
        CheckedNumericComputationAtom.numericScaleSummary
    | .fieldFilled field | .fieldNotFilled field =>
        (model.lookupUniqueId field).toOption.any (·.repeatableScope.isPrefixOf scope)
    | .fieldFill _ sources => !sources.isEmpty && sources.all (·.admitted model scope)
    | .groupPresence _ source => source.admitted model scope
    | .text comparison => model.admitsTextComparisonIn scope comparison
    | .scalar comparison => model.admitsScalarGuardIn scope comparison

def wellFormedBool (condition : CheckedComputationCondition model) : Bool :=
  condition.rowBoundBool []

/-- The operation context keeps filter reads distinct from selected-value reads. Guard atoms use
that same reader, so a `Having` source cannot silently switch to the selected-value view. -/
def evalCheckedIn (condition : CheckedComputationCondition model)
    (context : NumericComputationEvaluationContext) :
    Except CheckedComputationConditionError ComputationConditionResult :=
  let scalar := context.scalarContext model
  ComputationConditionOf.evalCheckedWith condition scalar CheckedComputationConditionError.primitive
    (fun atom => (context.readCheckedNumericComputationAtom atom).mapError .numeric)
    (fun source => (source.evalChecked scalar (some context.filterRead) context.indexColumn? (some context.filterStoredText) (some context.filterNumberText)).mapError .predicate)

/-- The addressed overlay carries completed producers into aggregate and filtered reads too.
The numeric operation reader owns empty substitution, reached poison and every atom's fold. -/
def evalChecked (condition : CheckedComputationCondition model)
    (context : ScalarComputationContext) (indexColumn? : Option SemanticIndexColumnReader := none) :
    Except CheckedComputationConditionError ComputationConditionResult :=
  match context.addressed with
  | some addressed => condition.evalCheckedIn {
      scalar := context, document := addressed.document, outer := context.row
      filterRead := addressed.read, filterStoredText := addressed.storedText, filterNumberText := addressed.numberText,
      starRead := addressed.read, starStoredText := addressed.storedText, indexColumn? }
  | none =>
      ComputationConditionOf.evalCheckedWith condition context CheckedComputationConditionError.primitive
        (fun atom => (context.readCheckedNumericComputationAtom atom).mapError .numeric)
        (fun source => (source.evalChecked context (indexColumn? := indexColumn?)).mapError .predicate)

def withCommon (common own : Option (CheckedComputationCondition model)) :
    Option (CheckedComputationCondition model) :=
  ComputationConditionOf.withCommon common own

private def liftAtom (model : FlatModel) : ComputationNumericAtom →
    Except CheckedComputationConditionElabError (CheckedNumericComputationAtom model)
  | .field source => do
      let declaration ← (model.lookupUniqueId source.id).mapError
        (CheckedComputationConditionElabError.primitive ∘ ComputationConditionElabError.resolve)
      if declaration.toNumberField? == some source then pure (.numeric (.field declaration))
      else throw .incoherent
  | .baseYear year => pure (.numeric (.baseYear year))
  | .repetition source =>
      if source.scope.isEmpty then
        pure (.numeric (.fixedCurrentRepetition { path := source.path, origin := .path }))
      else pure (.numeric (.boundCurrentRepetition source))

/-- Lift the established resolved guard without reparsing paths or weakening model ownership. -/
def ofLegacy (model : FlatModel) (condition : ComputationCondition) :
    Except CheckedComputationConditionElabError (CheckedComputationCondition model) :=
  ComputationConditionOf.mapNumericM (liftAtom model) (fun source => nomatch source) condition

end CheckedComputationCondition

namespace CheckedComputationAlternative

def expandCommonPrecondition (common : Option (CheckedComputationCondition model))
    (alternatives : List (CheckedComputationAlternative model Operation)) :
    List (CheckedComputationAlternative model Operation) :=
  alternatives.map fun alternative =>
    { alternative with precondition := CheckedComputationCondition.withCommon common alternative.precondition }

def selectFirstChecked (alternatives : List (CheckedComputationAlternative model Operation))
    (context : ScalarComputationContext) (indexColumn? : Option SemanticIndexColumnReader := none) :
    Except CheckedComputationConditionError (ComputationAlternativeSelection Operation) :=
  ComputationAlternative.selectFirstWith (fun condition => condition.evalChecked context indexColumn?) alternatives

def selectFirstCheckedIn (alternatives : List (CheckedComputationAlternative model Operation))
    (context : NumericComputationEvaluationContext) :
    Except CheckedComputationConditionError (ComputationAlternativeSelection Operation) :=
  ComputationAlternative.selectFirstWith (fun condition => condition.evalCheckedIn context) alternatives

def ofLegacy (model : FlatModel) (alternative : ComputationAlternative Operation) :
    Except CheckedComputationConditionElabError (CheckedComputationAlternative model Operation) := do
  let precondition ← alternative.precondition.mapM (CheckedComputationCondition.ofLegacy model)
  pure { precondition, operation := alternative.operation }

end CheckedComputationAlternative

private def FlatModel.elaborateCheckedNumericGuard (model : FlatModel)
    (declaringGroup targetGroup : GroupPath)
    (surface : NumericComparisonOf SurfaceNumericComputationAtom) :
    Except CheckedComputationConditionElabError (CheckedComputationCondition model) := do
  model.checkNumericOperationNodes declaringGroup targetGroup surface.left |>.mapError .numeric
  model.checkNumericOperationNodes declaringGroup targetGroup surface.right |>.mapError .numeric
  let left ← surface.left.mapM (model.elaborateNumericComputationAtom declaringGroup targetGroup)
    |>.mapError .numeric
  let right ← surface.right.mapM (model.elaborateNumericComputationAtom declaringGroup targetGroup)
    |>.mapError .numeric
  let comparison : NumericComparisonOf (CheckedNumericComputationAtom model) :=
    { left, right, op := surface.op, suppressExactScaleWarning := surface.suppressExactScaleWarning }
  if comparison.admittedWith
      (model.admitsNumericComputationOperand (model.repeatableScopeForGroupPath targetGroup))
      CheckedNumericComputationAtom.numericScaleSummary then
    pure (.leaf (.numeric comparison))
  else throw (.numeric .unsupportedExpression)

private def FlatModel.liftPrimitiveComputationGuard (model : FlatModel)
    (declaringGroup targetGroup : GroupPath) (surface : SurfaceComputationCondition) :
    Except CheckedComputationConditionElabError (CheckedComputationCondition model) := do
  let condition ← (model.elaborateComputationCondition declaringGroup targetGroup surface).mapError .primitive
  CheckedComputationCondition.ofLegacy model condition

/-- Resolve every target family's guards through one checked numeric and primitive boundary. -/
def FlatModel.elaborateCheckedComputationCondition (model : FlatModel)
    (declaringGroup targetGroup : GroupPath) :
    SurfaceComputationConditionOf SurfaceNumericComputationAtom SurfaceComputationPredicate →
      Except CheckedComputationConditionElabError (CheckedComputationCondition model)
  | .numeric comparison => model.elaborateCheckedNumericGuard declaringGroup targetGroup comparison
  | .predicate source => (.leaf ∘ .predicate) <$>
      ((model.elaborateComputationPredicate declaringGroup targetGroup source).mapError .predicate)
  | .fieldFilled field => model.liftPrimitiveComputationGuard declaringGroup targetGroup (.fieldFilled field)
  | .fieldNotFilled field => model.liftPrimitiveComputationGuard declaringGroup targetGroup (.fieldNotFilled field)
  | .text op left right => model.liftPrimitiveComputationGuard declaringGroup targetGroup (.text op left right)
  | .boolean op field expected => model.liftPrimitiveComputationGuard declaringGroup targetGroup (.boolean op field expected)
  | .fieldFill operator source => (.leaf ∘ .predicate) <$>
      ((model.elaborateComputationPredicate declaringGroup targetGroup (.fieldFill operator source)).mapError .predicate)
  | .groupPresence operator source => model.liftPrimitiveComputationGuard declaringGroup targetGroup (.groupPresence operator source)
  | .groupFill operator source =>
      (model.elaborateComputationGroupListWith declaringGroup targetGroup operator source (fun operand => do
        let pair (positive negative : CheckedComputationPredicate model) :
            CheckedComputationCondition model × CheckedComputationCondition model :=
          (.leaf (.predicate positive), .leaf (.predicate negative))
        match operand with
        | .indexed source => pure (pair (.indexedFieldPresence .filled source) (.indexedFieldPresence .notFilled source))
        | .keyed source =>
            if !source.isGroup then throw .unsupportedOperand
            pure (pair (.keyedGroupPresence .filled source .ordinaryList) (.keyedGroupPresence .notFilled source .ordinaryList))
        | _ => throw .unsupportedOperand)).mapError (.primitive ∘ .groupFill)
  | .and left right => do
      let left ← model.elaborateCheckedComputationCondition declaringGroup targetGroup left
      pure (.and left (← model.elaborateCheckedComputationCondition declaringGroup targetGroup right))
  | .or left right => do
      let left ← model.elaborateCheckedComputationCondition declaringGroup targetGroup left
      pure (.or left (← model.elaborateCheckedComputationCondition declaringGroup targetGroup right))

end A12Kernel
