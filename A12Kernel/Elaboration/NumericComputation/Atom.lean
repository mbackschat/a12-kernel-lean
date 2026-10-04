import A12Kernel.Elaboration.AddressedRepeatableTarget
import A12Kernel.Elaboration.DateRangeBoundComponent
import A12Kernel.Elaboration.FieldFillList
import A12Kernel.Elaboration.FirstFilledValue
import A12Kernel.Elaboration.NumericAggregate
import A12Kernel.Elaboration.LiteralComparisonDiagnostic
import A12Kernel.Elaboration.NumericComputation.OperationTyping
import A12Kernel.Elaboration.TokenValueCount
import A12Kernel.Elaboration.DistinctCountSource
import A12Kernel.Semantics.ComputationCondition
import A12Kernel.Semantics.NumericTarget

/-! # Numeric computation atoms, faults and elaboration errors

The vocabulary the numeric computation carrier elaborates into and refuses with: its surface and checked atoms, the faults its evaluation can raise, its elaboration errors, and the Kernel class each error projects. Elaboration itself lives in `NumericComputation/Core.lean`.

Numeric and Boolean/Confirm `NumberOfValueInFields` remain distinct checked atoms so their different field-kind matrices and per-cell provenance survive arithmetic, target evaluation, and generated validation without a second expression tree or aggregate fold.
-/

namespace A12Kernel

abbrev NumericComputationAtom := ResolvedNumericAtom FlatFieldDecl

/-- The complete computation surface keeps ordinary numeric atoms in their shared representation and adds distinct prefix-selecting and row-aligned aggregate atoms without creating another arithmetic tree. -/
inductive SurfaceNumericComputationAtom where
  | numeric (source : SurfaceNumericAtom SurfaceNumberEntitySource)
  | filledFieldCount (source : SurfaceFieldEntitySource)
  | firstFilled (source : SurfaceNumberEntitySource)
  | valueCount (expected : Rat) (source : SurfaceNumberEntitySource)
  | tokenValueCount (expected : String) (source : SurfaceTokenValueCountSource)
  /-- The token count over the shared entity-list shape, whose slots include a group, where the
  form above carries a category projection on a star instead. -/
  | tokenEntityValueCount (expected : String) (source : SurfaceTokenEntitySource)
  | booleanValueCount (expected : Bool)
      (source : SurfaceBooleanValueCountSource)
  | sumOfProducts (source : SurfaceNumericProductAggregate)
  deriving Repr, DecidableEq

/-- One checked numeric computation atom. Ordinary scalar/entity-list sources retain the shared resolved atom, `FirstFilledValue` and value count retain their distinct scans over that same entity-list source, and `SumOfProducts` retains its proof-bearing common-row plan. -/
inductive CheckedNumericComputationAtom (model : FlatModel) where
  | numeric
      (source : ResolvedNumericAtom FlatFieldDecl
        (CheckedNumberEntitySource model))
  | filledFieldCount (source : CheckedFieldFillList model)
  | firstFilled (source : CheckedNumberEntitySource model)
  | valueCount (expected : Rat) (source : CheckedNumberEntitySource model)
  | tokenDistinctCount (source : CheckedTokenEntitySource model)
  | temporalDistinctCount (run : CheckedTemporalDistinctCountRun model)
  | tokenValueCount (source : CheckedTokenValueCountSource model)
  | booleanValueCount (source : CheckedBooleanValueCountSource model)
  | sumOfProducts (source : CheckedNumericProductAggregate model)
  /-- A filled-group count whose operand list carries at least one star. The fixed-only list
  keeps the established `numeric` atom untouched, so widening this operator costs the
  already-measured form nothing. -/
  | filledGroupCountMixed (operands : List (CheckedGroupCountOperand model))

/-- Fail-closed faults outside the admitted numeric computation-expression fragment. -/
inductive NumericComputationFault where
  | guardBinding (error : ComputationConditionError)
  | stringExpression (error : StringComputationFault)
  | guardValueFailure
  | unsupportedGuardPredicate
  | fieldFillSource (error : FieldFillListElabError)
  | fieldKindMismatch (field : FieldId)
  | unsupportedDateCalendar
  | unsupportedDateTimeDifferenceOperand
  | worldRequired
  /-- One resolved group operand of a filled-group count lies outside the admitted scalar boundary.
  The path names *which* operand, so an Explain or Qualify consumer can point at it rather than at the
  whole count; the count itself is order-insensitive, so nothing else about the refusal is ordered. -/
  | unsupportedGroupCount (group : GroupPath)
  /-- The model-free resolved evaluator cannot enumerate any group's descendants, so no single operand
  is at fault. Kept distinct from the class above because the remedy differs: that one is an authoring
  boundary, this one a missing evaluation input. -/
  | groupCountNeedsModel
  | repeatableContextRequired
  | repeatableAddressing (error : StarAddressingError)
  deriving Repr, DecidableEq

/-- The bounded runtime inputs needed when one checked numeric expression contains repeatable entity-list atoms. This is an expression evaluator context, not a document scheduler or dependency overlay. -/
structure NumericComputationEvaluationContext where
  scalar : ScalarComputationContext
  document : Document
  outer : Env
  filterRead : Env → FieldId → CheckedCell
  starRead : Env → FieldId → CheckedCell

inductive NumericComputationElabError where
  /-- An operand's reference, or the declaring group's syntax. -/
  | resolve (error : ResolveError)
  /-- The target's own declaration, looked up by identity rather than by an authored path. -/
  | targetResolve (error : ResolveError)
  /-- The model fails its own validation before any operation is read. -/
  | invalidModel (error : ResolveError)
  | targetNotNumber (field : FieldId)
  | operandNotNumber (path : List String)
  /-- The operation's post-order node check refused it, its typing or one of its authoring gates, with
  the class of the node that failed first, `none` where that node's class is not measured. -/
  | operationNode (diagnostic : Option KernelStaticDiagnostic)
  | copyComparison (targetPath sourcePath : List String) (refusal : CopyComparisonRefusal)
  | lengthOperandNotEvaluatedString (path : List String)
  | rangeOperandNotString (path : List String)
  | invalidStringRange (start finish : Nat)
  | fieldValueAsNumberSource (path : List String)
      (error : FieldValueAsNumberSourceError)
  | incompatibleTemporalSource (path : List String)
  /-- The declared DateRange profile does not expose the requested date component at its
  endpoint; the same measured class the validation surface reports. -/
  | dateRangeBoundPartNotExposed (path : List String) (part : DateNumericPart)
  | incompatibleDateDifference
  | unsupportedCalendarProfile (zoneId : String)
  | baseYearNotDeclared
  | fieldFill (error : FieldFillListElabError)
  | aggregate (error : NumberEntityElabError)
  | tokenValueCount (error : TokenValueCountElabError)
  | booleanValueCount (error : BooleanValueCountElabError)
  | productAggregate (error : NumericProductAggregateElabError)
  | groupReference (error : FixedGroupReferenceError)
  | currentRepetitionSource (error : FixedGroupReferenceError)
  | groupCountNeedsMultipleOperands
  /-- The starred group plan itself refused; the underlying error carries the class. -/
  | starredGroupCountPlan (error : StarredGroupElabError)
  | overlappingGroupCountOperands (left right : GroupPath)
  /-- A root group beside any other operand. Reached only once containment is ruled out, because
  the Kernel checks the two gates in that order on both arms. -/
  | rootGroupInGroupCount (path : GroupPath)
  /-- An operand leaves a repeatable level for its evaluation to bind that the target's scope does
  not; the record carries what selects the class. -/
  | unboundOperandLevel (unbound : UnboundOperandLevel)
  | targetSelfReference (field : FieldId)
  | authoring (result : NumericAuthoringCheck)
  | unsupportedExpression
  | operationScaleMismatch (targetScale : Nat) (operation : NumericScaleSummary)
  | targetPolicyMismatch (target policy : NumField)
  /-- A row target's placement or repetition. -/
  | repeatableTarget (error : AddressedRepeatableTargetElabError)
  | incoherentCore
  deriving Repr, DecidableEq

namespace NumericComputationElabError

/-- Project the measured fixed filled-group computation admission failures to their exact
    Kernel diagnostic classes. Every other computation refusal remains unmapped. -/
def groupCountDiagnostic? :
    NumericComputationElabError → Option KernelStaticDiagnostic
  | .groupCountNeedsMultipleOperands => some .paramSizeInvalidGN
  -- The plan's empty-group class and the resolver classes are measured on this arm too, not
  -- borrowed from validation's
  -- ([empty](../../../docs/sources/static-admission-and-class-probes.md#src-entity-list-kind-empty-and-root-carriers),
  -- [resolver](../../../docs/sources/path-resolution-class-probes.md#src-group-operand-resolution-classes)).
  | .starredGroupCountPlan error => error.diagnostic?
  | .groupReference error => error.diagnostic?
  | .overlappingGroupCountOperands left right =>
      if left == right then some .duplicateParam1 else some .duplicateParam2
  | .rootGroupInGroupCount _ => some .rootGroupWithOtherParameters
  | _ => none

/-- Project the measured computed Number target-scale rejection, the class of the operation's first
failing node, a read of the target, which every measured shape reaches only past those gates,
aggregates, `FirstFilledValue` and group counts included, and a copied field the generated comparison
refuses ([checkpoint](../../../docs/sources/computation-scheduling-probes.md#src-join-operators-and-guards)).
The class is one operation's: a computation of several alternatives asks every alternative's other
gates before any read of the target, which `elaborateNumericTargetComputationTable` owns. The shared
authoring check this carrier also asks never answers first, because the node check raises each of its
refusals at the node it inspects, so its result stays unmapped with the other computation failures. -/
def targetDiagnostic? :
    NumericComputationElabError → Option KernelStaticDiagnostic
  | .operationScaleMismatch _ _ => some .invalidCompareDecimalPlaces
  | .copyComparison _ _ refusal => some refusal.diagnostic
  | .operationNode diagnostic => diagnostic
  | .targetSelfReference _ => some .errorReferenceToCalculatedField
  -- A row target's placement, measured on this carrier with a Number and a String copy and a
  -- guarded constant ([checkpoint](../../../docs/sources/computation-scheduling-probes.md#src-row-target-boundary)).
  | .repeatableTarget (.targetOutsideDeclaringGroup _ _) => some .fieldNotInRuleGroup
  | .repeatableTarget (.targetIsIndexField _) => some .errorIndexAsCalculatedField
  | _ => none

/-- Project the per-row operand gate, whether this arm, an operand's resolver or an entity list's
    shape asked it. The levels the target's scope holds are bound, so a read's class is decided by its
    first other level: containment when the target lies outside the declaring group, and otherwise
    where that level lies beside or below the target's group
    ([checkpoint](../../../docs/sources/group-list-and-capacity-probes.md#src-computation-star-binding-gate)). -/
def iterationDiagnostic? :
    NumericComputationElabError → Option KernelStaticDiagnostic
  | .unboundOperandLevel unbound
  | .resolve (.unboundOperandLevel _ unbound)
  | .groupReference (.unboundOperandLevel _ unbound)
  | .aggregate (.shape (.unboundOperandLevel unbound))
  | .tokenValueCount (.source (.shape (.unboundOperandLevel unbound)))
  | .booleanValueCount (.shape (.unboundOperandLevel unbound)) => unbound.diagnostic?
  | _ => none

/-- The Kernel class of one operation's refusal, through whichever of the projections above owns its
arm, or through the shared resolver projection for an operand's reference, whose classes the
computation carrier draws as every other carrier does
([checkpoint](../../../docs/sources/path-resolution-class-probes.md#src-resolver-failure-classes-every-carrier)).
The target's lookup and the model's own validation claim no class. -/
def diagnostic? (error : NumericComputationElabError) : Option KernelStaticDiagnostic :=
  error.targetDiagnostic? <|> error.iterationDiagnostic? <|> error.groupCountDiagnostic? <|>
    match error with
    | .resolve cause => cause.diagnostic?
    -- A `CurrentRepetition` naming no group, measured at a row target
    -- ([checkpoint](../../../docs/sources/computation-scheduling-probes.md#src-row-target-boundary)).
    | .currentRepetitionSource (.unknownGroup _) => some .invalidEntity
    | _ => none

end NumericComputationElabError

end A12Kernel
