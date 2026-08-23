import A12Kernel.Elaboration.DateRangeStoredComparison
import A12Kernel.Elaboration.DateRangeOverlap

/-! # DateRange conditions read at a rule's iterating row

The DateRange condition carriers differ in what they compare — two stored ranges, one endpoint
against a fixed date, two endpoints, an overlap scan — but they read their operands the same way: at
one reading scope, at the row the enclosing rule is currently evaluating. This module owns that
common shape so the checked condition tree carries one leaf family rather than one per carrier, and
so a new carrier lands as a member here instead of as another set of dispatch arms.

The reading scope is the enclosing rule's own iteration scope. Admission is therefore the measured
locus rule stated positively: an operand is accepted exactly when that scope binds every repeatable
level the operand crosses. Each member's own comparison, component, and emptiness behaviour stays
with its carrier, so this module decides nothing about meaning beyond who reads which cell.
-/

namespace A12Kernel

/-- One DateRange condition whose operands are read at the enclosing rule's current row. -/
inductive IteratedDateRangeCondition (model : FlatModel) where
  | storedEquality (comparison : CheckedIteratedDateRangeComparison model)
  | boundAgainstFixed (operand : CheckedIteratedDateRangeBound model)
      (position : DateRangeBoundComparisonPosition)
      (comparison : TemporalComparisonOp) (expected : FullDate)
  | boundPair (left right : CheckedIteratedDateRangeBound model)
      (comparison : TemporalComparisonOp)
  | overlap (source : CheckedDateRangesOverlapSource model)

/-- Static refusal while resolving one iterated DateRange condition. -/
inductive IteratedDateRangeConditionElabError where
  | storedEquality (cause : DirectDateRangeComparisonElabError)
  | operand (cause : DirectDateRangeElabError)
  | formatsNotComparable (left right : TemporalComponents)
  | overlap (cause : DateRangesOverlapElabError)
  deriving Repr, DecidableEq

namespace IteratedDateRangeConditionElabError

/-- Project each member's own established diagnostic. The operand classes are the shared DateRange
source owner's, so a repeatable operand crossing an unbound level reports the Kernel's
missing-wildcard class here exactly as it does on the scalar carriers. -/
def diagnostic? :
    IteratedDateRangeConditionElabError → Option KernelStaticDiagnostic
  | .storedEquality cause => cause.diagnostic?
  | .operand cause => cause.diagnostic?
  | .formatsNotComparable _ _ => some .invalidCompareToDate
  | .overlap cause => cause.diagnostic?

end IteratedDateRangeConditionElabError

namespace IteratedDateRangeCondition

/-- Every operand declaration this condition reads, in authored order. -/
def operandDeclarations : IteratedDateRangeCondition model → List FlatFieldDecl
  | .storedEquality comparison =>
      [comparison.left.declaration, comparison.right.declaration]
  | .boundAgainstFixed operand _ _ _ => [operand.declaration]
  | .boundPair left right _ => [left.declaration, right.declaration]
  | .overlap source =>
      -- Only the unstarred operands are read at the enclosing row. A starred operand reopens its
      -- own levels, so it is neither bound by the reading scope nor a contributor to it.
      source.shape.operands.filterMap fun operand =>
        match operand with
        | .field declaration _ => some declaration
        | _ => none

/-- The operands that actually cross a repeatable level. These are the declarations the enclosing
rule resolves before evaluation and the levels it derives its iteration from. -/
def repeatableDeclarations (condition : IteratedDateRangeCondition model) :
    List FlatFieldDecl :=
  condition.operandDeclarations.filter fun declaration =>
    !declaration.repeatableScope.isEmpty

/-- Whether every retained declaration is still the model's own and still bound by the reading
group's scope. The checked condition re-establishes this at assembly, so a leaf cannot smuggle a
stale declaration or an unbound level past the locus gate. -/
def wellFormedIn (condition : IteratedDateRangeCondition model)
    (scope : List RepeatableLevel) : Bool :=
  !condition.repeatableDeclarations.isEmpty &&
    condition.operandDeclarations.all fun declaration =>
      declaration.repetitionBoundBy scope &&
        match model.lookupUniqueId declaration.id with
        | .ok owned => owned == declaration
        | .error _ => false

/-- Produce this condition's verdict at the consuming row. The cell read is a parameter because its
failure channel belongs to the enclosing leaf, which owns the row environment; the overlap member
additionally needs the document, because a starred operand's extent is a stream of rows rather than
one cell. Each member then reuses its own carrier's comparison or scan unchanged. -/
def verdictOf (condition : IteratedDateRangeCondition model)
    (document : CheckedDocument model) (outer : Env)
    (read : FieldId → Except CheckedAddressingError CheckedCell) :
    Except CheckedAddressingError Verdict :=
  match condition with
  | .storedEquality comparison => do
      let left ← read comparison.left.declaration.id
      let right ← read comparison.right.declaration.id
      pure (comparison.verdictOf (observeIteratedDateRangeOperand left)
        (observeIteratedDateRangeOperand right))
  | .boundAgainstFixed operand position comparison expected => do
      let cell ← read operand.declaration.id
      pure (position.evalAgainstFixed comparison expected
        (operand.selectFrom cell))
  | .boundPair left right comparison => do
      let leftCell ← read left.declaration.id
      let rightCell ← read right.declaration.id
      pure (comparison.evalObserved (left.selectFrom leftCell)
        (right.selectFrom rightCell))
  | .overlap source => do
      let cores ← source.operands.mapM fun operand =>
        operand.resolveValidationCore document outer
      pure (evalDateRangesOverlap
        (cores.map totalCheckedDateRangeOperandSemantic))

end IteratedDateRangeCondition

/-- Resolve one stored-versus-stored equality read at the rule's row. -/
def elaborateIteratedStoredEquality (model : FlatModel)
    (scope : List RepeatableLevel) (left right : FieldId)
    (comparison : EqualityOp) :
    Except IteratedDateRangeConditionElabError
      (IteratedDateRangeCondition model) :=
  (.storedEquality <$>
    elaborateIteratedDateRangeComparison model scope left right comparison)
    |>.mapError .storedEquality

/-- Resolve one selected endpoint compared against a fixed complete date. -/
def elaborateIteratedBoundAgainstFixed (model : FlatModel)
    (scope : List RepeatableLevel) (source : FieldId) (bound : DateRangeBound)
    (position : DateRangeBoundComparisonPosition)
    (comparison : TemporalComparisonOp) (expected : FullDate) :
    Except IteratedDateRangeConditionElabError
      (IteratedDateRangeCondition model) := do
  let operand ←
    (elaborateIteratedDateRangeBound model scope source bound).mapError .operand
  pure (.boundAgainstFixed operand position comparison expected)

/-- Resolve two selected endpoints compared with each other. Comparability is the ordinary temporal
rule over the two declarations' component sets, so this carrier adds no gate of its own. -/
def elaborateIteratedBoundPair (model : FlatModel)
    (scope : List RepeatableLevel)
    (leftSource : FieldId) (leftBound : DateRangeBound)
    (rightSource : FieldId) (rightBound : DateRangeBound)
    (comparison : TemporalComparisonOp) :
    Except IteratedDateRangeConditionElabError
      (IteratedDateRangeCondition model) := do
  let left ←
    (elaborateIteratedDateRangeBound model scope leftSource leftBound).mapError
      .operand
  let right ←
    (elaborateIteratedDateRangeBound model scope rightSource rightBound).mapError
      .operand
  if comparison.admitsFormats model.baseYear.isSome left.format.components
      right.format.components then
    pure (.boundPair left right comparison)
  else
    throw (.formatsNotComparable left.format.components right.format.components)

/-- Resolve one singular overlap predicate whose unstarred operands the rule's own iteration may
cross. Every gate is the scalar operator's, including the group refusal and the uniform-year rule;
only the operand-locus admission widens. A starred operand keeps its own topology, so a list mixing
a starred and an unstarred occurrence of one field is admitted here exactly as the Kernel admits it,
with the star reopening the level the bare operand reads at the current row. -/
def elaborateIteratedOverlap (model : FlatModel) (declaringGroup : GroupPath)
    (scope : List RepeatableLevel) (authored : SurfaceFieldEntitySource) :
    Except IteratedDateRangeConditionElabError
      (IteratedDateRangeCondition model) :=
  (.overlap <$>
    elaborateDateRangesOverlapSourceIn model declaringGroup scope authored)
    |>.mapError .overlap

end A12Kernel
