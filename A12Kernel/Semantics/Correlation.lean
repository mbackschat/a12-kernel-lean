import A12Kernel.Semantics.Iteration

/-! # A12Kernel.Semantics.Correlation — captured outer `$` inside Having

This validation-only capsule gives `$` its direct nested-loop meaning for one repeatable
group. Reference origins exist only in this filter AST: ordinary references read the
candidate/inner row and `$` references read the explicitly captured outer rule row.
-/

namespace A12Kernel

/-- Origin of one reference inside a correlated `Having` condition. -/
inductive HavingOrigin where
  | inner
  | outer
  deriving Repr, DecidableEq

/-- The comparison subset needed to separate inner/outer routing and self-exclusion. -/
inductive CorrelationComparisonOp where
  | equal
  | notEqual
  | lessThan
  deriving Repr, DecidableEq

structure HavingNumberRef where
  origin : HavingOrigin
  field : FlatNumberField
  deriving Repr, DecidableEq

/-- One correlated filter frame: both row identities are explicit and neither is an
    ambient implicit "current" row. -/
structure SingleGroupFilterFrame where
  innerRow : RowIndex
  outerRow : RowIndex
  deriving Repr, DecidableEq

def SingleGroupFilterFrame.rowAt (frame : SingleGroupFilterFrame) :
    HavingOrigin → RowIndex
  | .inner => frame.innerRow
  | .outer => frame.outerRow

def SingleGroupFilterFrame.innerEnv (frame : SingleGroupFilterFrame)
    (context : SingleGroupValidationContext) : Env :=
  context.envAt frame.innerRow

def SingleGroupFilterFrame.outerEnv (frame : SingleGroupFilterFrame)
    (context : SingleGroupValidationContext) : Env :=
  context.envAt frame.outerRow

structure CapturedSingleGroupContext where
  rows : SingleGroupValidationContext
  outerRow : RowIndex

def CapturedSingleGroupContext.frame (context : CapturedSingleGroupContext)
    (innerRow : RowIndex) : SingleGroupFilterFrame :=
  { innerRow, outerRow := context.outerRow }

/-- Closed filter-only AST. An outer reference cannot escape into `FlatCondition` or any
    ordinary rule expression through this type. -/
inductive CorrelatedHaving where
  | compareNumbers (op : CorrelationComparisonOp)
      (left right : HavingNumberRef)
  | compareRepetitions (op : CorrelationComparisonOp)
      (left right : HavingOrigin)
  | and (left right : CorrelatedHaving)
  deriving Repr, DecidableEq

private def HavingOrigin.isInner : HavingOrigin → Bool
  | .inner => true
  | .outer => false

private def HavingOrigin.isOuter : HavingOrigin → Bool
  | .inner => false
  | .outer => true

def CorrelatedHaving.usesInner : CorrelatedHaving → Bool
  | .compareNumbers _ left right => left.origin.isInner || right.origin.isInner
  | .compareRepetitions _ left right => left.isInner || right.isInner
  | .and left right => left.usesInner || right.usesInner

def CorrelatedHaving.usesOuter : CorrelatedHaving → Bool
  | .compareNumbers _ left right => left.origin.isOuter || right.origin.isOuter
  | .compareRepetitions _ left right => left.isOuter || right.isOuter
  | .and left right => left.usesOuter || right.usesOuter

/-- Proof that a filter genuinely uses both environments. This is only the origin check;
    field scope, path legality, and equality-scale legality belong to repeatable
    elaboration and are not claimed by this wrapper. -/
structure OriginCheckedCorrelatedHaving where
  condition : CorrelatedHaving
  usesInner : condition.usesInner = true
  usesOuter : condition.usesOuter = true

inductive CorrelationCheckError where
  | missingInner
  | missingOuter
  deriving Repr, DecidableEq

/-- Fail closed on an all-`$` filter or on a condition that is not actually correlated.
    Other authoring restrictions remain unrepresentable in the closed AST or belong to
    the later repeatable elaborator. -/
def CorrelatedHaving.check (condition : CorrelatedHaving) :
    Except CorrelationCheckError OriginCheckedCorrelatedHaving :=
  if inner : condition.usesInner then
    if outer : condition.usesOuter then
      .ok { condition, usesInner := inner, usesOuter := outer }
    else
      .error .missingOuter
  else
    .error .missingInner

inductive CorrelatedNumberOperand where
  | value (amount : Rat)
  | unknown (cause : FormalCause)
  deriving Repr, DecidableEq

/-- Resolve one numeric filter reference at its declared origin. Empty-to-zero is local
    to numeric comparison; formal invalidity remains explicit. -/
def HavingNumberRef.resolve (reference : HavingNumberRef)
    (context : SingleGroupValidationContext) (frame : SingleGroupFilterFrame) :
    CorrelatedNumberOperand :=
  let rowContext : FlatContext :=
    { read := context.read (frame.rowAt reference.origin) }
  match rowContext.resolveNumberComparisonOperand reference.field with
  | .value amount _ => .value amount
  | .unknown cause => .unknown cause
  | .notEvaluated => .unknown .malformed

def CorrelationComparisonOp.holdsRat (op : CorrelationComparisonOp)
    (left right : Rat) : Bool :=
  let left := rescaleHalfUp left comparisonScale
  let right := rescaleHalfUp right comparisonScale
  match op with
  | .equal => left == right
  | .notEqual => left != right
  | .lessThan => left < right

def CorrelationComparisonOp.holdsRow (op : CorrelationComparisonOp)
    (left right : RowIndex) : Bool :=
  match op with
  | .equal => left == right
  | .notEqual => left != right
  | .lessThan => left < right

def CorrelationComparisonOp.evalOperands (op : CorrelationComparisonOp)
    (left right : CorrelatedNumberOperand) : K :=
  match left, right with
  | .value left, .value right => if op.holdsRat left right then .tru else .fls
  | _, _ => .unknown

/-- Truth of a correlated filter. Numeric empty operands use the comparison-local zero
    substitution; invalid operands are unknown; only the later selector decides that
    unknown is not kept. -/
def CorrelatedHaving.evalTruth (context : SingleGroupValidationContext)
    (frame : SingleGroupFilterFrame) : CorrelatedHaving → K
  | .compareNumbers op left right =>
      op.evalOperands (left.resolve context frame) (right.resolve context frame)
  | .compareRepetitions op left right =>
      if op.holdsRow (frame.rowAt left) (frame.rowAt right) then .tru else .fls
  | .and left right =>
      K.and (left.evalTruth context frame) (right.evalTruth context frame)

/-- Declarative truth predicate for the correlated filter. Atomic comparisons are
    stated over resolved values/rows, independently of the executable `Bool`; `And`
    remains structural. -/
def CorrelatedHaving.Holds (context : SingleGroupValidationContext)
    (frame : SingleGroupFilterFrame) : CorrelatedHaving → Prop
  | .compareNumbers op left right =>
      ∃ leftValue rightValue,
        left.resolve context frame = .value leftValue ∧
        right.resolve context frame = .value rightValue ∧
        op.holdsRat leftValue rightValue = true
  | .compareRepetitions op left right =>
      op.holdsRow (frame.rowAt left) (frame.rowAt right) = true
  | .and left right => left.Holds context frame ∧ right.Holds context frame

structure SingleCorrelatedStar where
  valueField : FlatNumberField
  having : OriginCheckedCorrelatedHaving

def SingleCorrelatedStar.keeps (star : SingleCorrelatedStar)
    (context : CapturedSingleGroupContext) (innerRow : RowIndex) : Bool :=
  star.having.condition.evalTruth context.rows (context.frame innerRow) == .tru

/-- Naive reference meaning: for one captured outer row, scan every same-group candidate
    in document order. No self-exclusion and no hash-join optimization are implicit. -/
def SingleCorrelatedStar.select (star : SingleCorrelatedStar)
    (context : CapturedSingleGroupContext) : List RowIndex :=
  context.rows.candidates.filter (star.keeps context)

/-- Independent ordered keep/drop relation for one captured outer row. -/
inductive SelectCorrelatedRows (star : SingleCorrelatedStar)
    (context : CapturedSingleGroupContext) : List RowIndex → List RowIndex → Prop where
  | nil : SelectCorrelatedRows star context [] []
  | keep
      (kept : star.having.condition.Holds context.rows (context.frame row))
      (tail : SelectCorrelatedRows star context rows selected) :
      SelectCorrelatedRows star context (row :: rows) (row :: selected)
  | drop
      (dropped : ¬star.having.condition.Holds context.rows (context.frame row))
      (tail : SelectCorrelatedRows star context rows selected) :
      SelectCorrelatedRows star context (row :: rows) selected

/-- Validation presence of one typed Number cell for the narrow selected-presence
    consumer. -/
def FlatNumberField.filledTruthAt (field : FlatNumberField)
    (context : SingleGroupValidationContext) (row : RowIndex) : K :=
  match observeCell .validation (context.read row field.id) with
  | .empty => .fls
  | .value _ => .tru
  | .unknown _ | .poison _ => .unknown

/-- Fold validation presence over exactly the supplied ordered rows. -/
def FlatNumberField.anyFilledTruth (field : FlatNumberField)
    (context : SingleGroupValidationContext) : List RowIndex → K
  | [] => .fls
  | row :: rest =>
      K.or (field.filledTruthAt context row) (field.anyFilledTruth context rest)

/-- Evaluate selected Number-cell presence only after correlated filtering. -/
def SingleCorrelatedStar.evalSelectedAnyFilled (star : SingleCorrelatedStar)
    (context : CapturedSingleGroupContext) : K :=
  star.valueField.anyFilledTruth context.rows (star.select context)

/-- Narrow rule observer with an explicitly supplied outer guard field:
    `FieldFilled(outer Guard) And AtLeastOneFieldFilled(G*/F Having filter)`. The
    presence consumer classifies `F` only after selection; the filter may independently
    reference the same field. The API does not require the guard and `F` to differ. -/
def SingleCorrelatedStar.evalGuardedAnyFilledOn (star : SingleCorrelatedStar)
    (guardField : FlatNumberField) (context : CapturedSingleGroupContext) : K :=
  K.and
    (guardField.filledTruthAt context.rows context.outerRow)
    (star.evalSelectedAnyFilled context)

/-- Convenience form for the earlier same-field retained rule shape. -/
def SingleCorrelatedStar.evalGuardedAnyFilled (star : SingleCorrelatedStar)
    (context : CapturedSingleGroupContext) : K :=
  star.evalGuardedAnyFilledOn star.valueField context

/-- Evaluate the guarded selected-presence observer for every outer row, preserving
    candidate order and retaining exactly the rows where its truth is definite true. -/
def SingleCorrelatedStar.firingRowsOn (star : SingleCorrelatedStar)
    (guardField : FlatNumberField)
    (context : SingleGroupValidationContext) : List RowIndex :=
  context.candidates.filter fun outerRow =>
    star.evalGuardedAnyFilledOn guardField { rows := context, outerRow } == .tru

/-- Convenience firing-row observer for the earlier same guard/consumer rule shape. -/
def SingleCorrelatedStar.firingRows (star : SingleCorrelatedStar)
    (context : SingleGroupValidationContext) : List RowIndex :=
  star.firingRowsOn star.valueField context

end A12Kernel
