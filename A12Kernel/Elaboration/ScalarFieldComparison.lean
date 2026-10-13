import A12Kernel.Elaboration.DateRangeStoredComparison
import A12Kernel.Elaboration.Flat.FieldValueRead

namespace A12Kernel

inductive ScalarFieldComparisonElabError where
  | read (error : ResolveError)
  | admission (diagnostic : KernelStaticDiagnostic)
  | range (error : DirectDateRangeComparisonElabError)
  deriving Repr, DecidableEq

/-- Boolean identity retains the declaration kind because Confirm alone substitutes false for
an empty cell (spec/02 §A.3; comparison-guard grid, 2026-10-04). -/
structure CheckedBooleanFieldComparison (model : FlatModel) where
  private mk ::
  left : FlatFieldDecl
  right : FlatFieldDecl
  operator : EqualityOp
  confirm : Bool

inductive CheckedScalarFieldComparison (model : FlatModel) where
  | boolean (source : CheckedBooleanFieldComparison model)
  | range (source : CheckedDateRangeSourceComparison model)

/-- The kind arms of a field pair, once both reads passed. `read` is the caller's bound read and
`rangeScope` the repeatable scope its DateRange operands are admitted at, so a computation guard and
a rule share one kind arm. -/
def elaborateScalarFieldComparisonWith (model : FlatModel)
    (read : SurfaceFieldPath → Except ResolveError FlatFieldDecl) (rangeScope : List RepeatableLevel)
    (operator : SurfaceComparisonOp) (left right : SurfaceFieldPath) :
    Except ScalarFieldComparisonElabError (CheckedScalarFieldComparison model) := do
  let left ← (read left).mapError .read
  let right ← (read right).mapError .read
  let some equality := operator.toEquality? | throw (.admission .invalidTypeForComparison)
  match left.policy.kind, right.policy.kind with
  | .boolean, .boolean => pure (.boolean { left, right, operator := equality, confirm := false })
  | .confirm, .confirm =>
      if equality == .equal then throw (.admission .invalidCompareToYes)
      pure (.boolean { left, right, operator := equality, confirm := true })
  | .confirm, _ | _, .confirm => throw (.admission .invalidCompareToYes)
  | .boolean, _ | _, .boolean => throw (.admission .invalidCompareToYesNo)
  | .dateRange, .dateRange =>
      .range <$> (elaborateDateRangeSourceComparisonIn model rangeScope left.id right.id equality).mapError .range
  | _, _ => throw (.admission .invalidCompareToDateRange)

def elaborateScalarFieldComparison (model : FlatModel) (declaringGroup targetGroup : GroupPath)
    (operator : SurfaceComparisonOp) (left right : SurfaceFieldPath) :
    Except ScalarFieldComparisonElabError (CheckedScalarFieldComparison model) :=
  elaborateScalarFieldComparisonWith model (model.resolveComputationFieldValueRead declaringGroup targetGroup)
    (model.repeatableScopeForGroupPath targetGroup) operator left right

private def CheckedBooleanFieldComparison.operands (source : CheckedBooleanFieldComparison model) :
    FlatBooleanOperand × FlatBooleanOperand :=
  let operand (field : FlatFieldDecl) : FlatBooleanOperand :=
    if source.confirm then .confirm { id := field.id } else .boolean { id := field.id }
  (operand source.left, operand source.right)

def CheckedBooleanFieldComparison.toFlat (source : CheckedBooleanFieldComparison model) : FlatComparison :=
  let (left, right) := source.operands
  .booleanFields source.operator left right

namespace CheckedScalarFieldComparison

def fields : CheckedScalarFieldComparison model → List FlatFieldDecl
  | .boolean source => [source.left, source.right]
  | .range source => [source.left.declaration, source.right.declaration]

def referencesField (source : CheckedScalarFieldComparison model) (field : FieldId) : Bool :=
  source.fields.any (·.id == field)

def rowBoundBool (source : CheckedScalarFieldComparison model) (scope : List RepeatableLevel) : Bool :=
  source.fields.all fun field =>
    (model.lookupUniqueId field.id).toOption == some field && field.repeatableScope.isPrefixOf scope

/-- The guard consumes typed observations with the shared ordered comparison; DateRange identity
uses the same endpoint/profile equality as validation, not stored-text equality. -/
def evalComputation (source : CheckedScalarFieldComparison model) (context : FlatContext) :
    Except FieldId ComputationConditionResult :=
  match source with
  | .boolean source =>
      let (left, right) := source.operands
      pure (evalComputationComparison (fun left right => source.operator.holds (left == right))
        (left.resolveAt .computation context) (right.resolveAt .computation context))
  | .range source =>
      let read (field : FieldId) := (CheckedDateRangeSource.observeRange field .computation
        (context.read field)).mapError (fun _ => field) |>.map CellObservation.asValidationSimpleOperand
      evalComputationComparisonExcept
        (fun left right => source.comparison.holds (left.sameIdentity right))
        (read source.left.declaration.id) (fun _ => read source.right.declaration.id)

end CheckedScalarFieldComparison
end A12Kernel
