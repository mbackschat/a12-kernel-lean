import A12Kernel.Semantics.Condition
import A12Kernel.Semantics.Iteration

/-! # A12Kernel.Semantics.Correlation — captured outer `$` inside Having

This validation-only core gives `$` its direct nested-loop meaning through explicit
candidate and captured repetition environments. Reference origins exist only in this
filter AST: ordinary references read the candidate environment and `$` references read
the explicitly captured outer rule environment. The established one-group API remains
an adapter over this shared core.
-/

namespace A12Kernel

/-- Origin of one reference inside a correlated `Having` condition. -/
inductive HavingOrigin where
  | inner
  | outer
  deriving Repr, DecidableEq

/-- Resolve exactly one binding for a repeatable level. Missing and duplicate bindings
    both fail closed; correlation must never guess a first row or substitute row zero. -/
def Env.uniqueRowAt? (env : Env) (level : RepeatableLevel) : Option RowIndex :=
  match env with
  | [] => none
  | (boundLevel, row) :: rest =>
      if boundLevel == level then
        if rest.any (fun binding => binding.1 == level) then none else some row
      else
        Env.uniqueRowAt? rest level

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

/-- A structural repetition reference retains the resolved level. The one-group capsule
    previously erased it because only one coordinate existed. -/
structure HavingRepetitionRef where
  origin : HavingOrigin
  level : RepeatableLevel
  deriving Repr, DecidableEq

/-- One correlated filter frame. Both candidate and captured rule environments are
    explicit full repetition contexts. -/
structure CorrelationFrame where
  innerEnv : Env
  outerEnv : Env
  deriving Repr, DecidableEq

def CorrelationFrame.envAt (frame : CorrelationFrame) : HavingOrigin → Env
  | .inner => frame.innerEnv
  | .outer => frame.outerEnv

def CorrelationFrame.rowAt? (frame : CorrelationFrame)
    (reference : HavingRepetitionRef) : Option RowIndex :=
  (frame.envAt reference.origin).uniqueRowAt? reference.level

/-- One correlated filter frame: both row identities are explicit and neither is an
    ambient implicit "current" row. This remains the one-group adapter. -/
structure SingleGroupFilterFrame where
  innerRow : RowIndex
  outerRow : RowIndex
  deriving Repr, DecidableEq

def SingleGroupFilterFrame.toCorrelationFrame (frame : SingleGroupFilterFrame)
    (context : SingleGroupValidationContext) : CorrelationFrame :=
  { innerEnv := context.envAt frame.innerRow
    outerEnv := context.envAt frame.outerRow }

structure CapturedSingleGroupContext where
  rows : SingleGroupValidationContext
  outerRow : RowIndex

def CapturedSingleGroupContext.frame (context : CapturedSingleGroupContext)
    (innerRow : RowIndex) : SingleGroupFilterFrame :=
  { innerRow, outerRow := context.outerRow }

/-- Closed filter-only leaves. An outer reference cannot escape into an ordinary rule expression through this type; connective structure comes from the shared `ConditionTree`. -/
inductive CorrelatedHavingLeaf where
  | compareNumbers (op : CorrelationComparisonOp)
      (left right : HavingNumberRef)
  | compareRepetitions (op : CorrelationComparisonOp)
      (left right : HavingRepetitionRef)
  deriving Repr, DecidableEq

/-- A correlated filter reuses the common connective tree while retaining its environment-sensitive leaf domain. -/
abbrev CorrelatedHaving := ConditionTree CorrelatedHavingLeaf

namespace CorrelatedHaving

def compareNumbers (op : CorrelationComparisonOp)
    (left right : HavingNumberRef) : CorrelatedHaving :=
  .leaf (.compareNumbers op left right)

def compareRepetitions (op : CorrelationComparisonOp)
    (left right : HavingRepetitionRef) : CorrelatedHaving :=
  .leaf (.compareRepetitions op left right)

def referencesField (condition : CorrelatedHaving) (field : FieldId) : Bool :=
  condition.anyLeaf fun
    | .compareNumbers _ left right =>
        left.field.id == field || right.field.id == field
    | .compareRepetitions _ _ _ => false

end CorrelatedHaving

private def HavingOrigin.isInner : HavingOrigin → Bool
  | .inner => true
  | .outer => false

private def HavingOrigin.isOuter : HavingOrigin → Bool
  | .inner => false
  | .outer => true

private def CorrelatedHavingLeaf.usesInner : CorrelatedHavingLeaf → Bool
  | .compareNumbers _ left right => left.origin.isInner || right.origin.isInner
  | .compareRepetitions _ left right => left.origin.isInner || right.origin.isInner

private def CorrelatedHavingLeaf.usesOuter : CorrelatedHavingLeaf → Bool
  | .compareNumbers _ left right => left.origin.isOuter || right.origin.isOuter
  | .compareRepetitions _ left right => left.origin.isOuter || right.origin.isOuter

def CorrelatedHaving.usesInner (condition : CorrelatedHaving) : Bool :=
  condition.anyLeaf CorrelatedHavingLeaf.usesInner

def CorrelatedHaving.usesOuter (condition : CorrelatedHaving) : Bool :=
  condition.anyLeaf CorrelatedHavingLeaf.usesOuter

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

/-- The only document operation needed by the shared correlation evaluator. Topology
    adapters construct environments; this seam reads a checked field through one. -/
structure CorrelationContext where
  read : Env → FieldId → CheckedCell

/-- Resolve one numeric filter reference through the selected environment and caller-selected phase. Empty-to-zero is local to numeric comparison; formal invalidity retains its cause for the consuming phase projection. -/
def HavingNumberRef.resolveInAt (reference : HavingNumberRef) (phase : Phase)
    (context : CorrelationContext) (frame : CorrelationFrame) :
    CorrelatedNumberOperand :=
  let rowContext : FlatContext :=
    { read := context.read (frame.envAt reference.origin) }
  match rowContext.resolveNumberComparisonOperandAt phase reference.field with
  | .value amount _ => .value amount
  | .unknown cause => .unknown cause

/-- Validation specialization retained for established filter consumers. -/
def HavingNumberRef.resolveIn (reference : HavingNumberRef)
    (context : CorrelationContext) (frame : CorrelationFrame) :
    CorrelatedNumberOperand :=
  reference.resolveInAt .validation context frame

private def malformedCorrelationCell : CheckedCell :=
  { rawPresent := true, parsed := none, findings := [.malformed] }

def SingleGroupValidationContext.asCorrelationContext
    (context : SingleGroupValidationContext) : CorrelationContext where
  read env field :=
    match env.uniqueRowAt? context.group with
    | some row => context.read row field
    | none => malformedCorrelationCell

/-- Backwards-compatible one-group numeric resolution. -/
def HavingNumberRef.resolve (reference : HavingNumberRef)
    (context : SingleGroupValidationContext) (frame : SingleGroupFilterFrame) :
    CorrelatedNumberOperand :=
  reference.resolveIn context.asCorrelationContext (frame.toCorrelationFrame context)

def CorrelationComparisonOp.holdsRat (op : CorrelationComparisonOp)
    (left right : Rat) : Bool :=
  match op with
  | .equal => NumericComparisonOp.equal.holds left right
  | .notEqual => NumericComparisonOp.notEqual.holds left right
  | .lessThan => NumericComparisonOp.less.holds left right

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

def CorrelationComparisonOp.evalRows (op : CorrelationComparisonOp)
    (left right : Option RowIndex) : K :=
  match left, right with
  | some left, some right => if op.holdsRow left right then .tru else .fls
  | _, _ => .unknown

def CorrelatedHavingLeaf.evalTruthIn (context : CorrelationContext)
    (frame : CorrelationFrame) : CorrelatedHavingLeaf → K
  | .compareNumbers op left right =>
      op.evalOperands (left.resolveIn context frame) (right.resolveIn context frame)
  | .compareRepetitions op left right =>
      op.evalRows (frame.rowAt? left) (frame.rowAt? right)

/-- Truth of a correlated filter. Numeric empty operands use the comparison-local zero substitution; invalid operands are unknown; only the later selector decides that unknown is not kept. Connectives use the shared strong-Kleene tree evaluator. -/
def CorrelatedHaving.evalTruthIn (condition : CorrelatedHaving)
    (context : CorrelationContext) (frame : CorrelationFrame) : K :=
  condition.evalK (CorrelatedHavingLeaf.evalTruthIn context frame)

/-- Evaluate one filter leaf during computation. Numeric reads are explicitly left-to-right: a poisoned left operand prevents the right read, while a clean missing repetition comparison merely fails to keep its candidate. -/
def CorrelatedHavingLeaf.evalComputationIn (context : CorrelationContext)
    (frame : CorrelationFrame) : CorrelatedHavingLeaf →
      ComputationConditionResult
  | .compareNumbers op left right =>
      match left.resolveInAt .computation context frame with
      | .unknown cause => .poison cause
      | .value leftValue =>
          match right.resolveInAt .computation context frame with
          | .unknown cause => .poison cause
          | .value rightValue =>
              if op.holdsRat leftValue rightValue then .holds else .notTrue
  | .compareRepetitions op left right =>
      match frame.rowAt? left with
      | none => .notTrue
      | some leftRow =>
          match frame.rowAt? right with
          | none => .notTrue
          | some rightRow =>
              if op.holdsRow leftRow rightRow then .holds else .notTrue

/-- Computation filters reuse the common connective tree but preserve first reached poison instead of validation's unknown-as-drop projection. -/
def CorrelatedHaving.evalComputationIn (condition : CorrelatedHaving)
    (context : CorrelationContext) (frame : CorrelationFrame) :
    ComputationConditionResult :=
  condition.evalComputation
    (CorrelatedHavingLeaf.evalComputationIn context frame)

/-- Keep one already-resolved candidate environment exactly when the filter is known true. The candidate and captured environments remain separate full repetition identities; false and UNKNOWN both drop the candidate. -/
def CorrelatedHaving.keepsEnvironment (condition : CorrelatedHaving)
    (context : CorrelationContext) (outerEnv innerEnv : Env) : Bool :=
  condition.evalTruthIn context { innerEnv, outerEnv } == .tru

/-- Select resolved candidate environments in their supplied semantic order before a consumer reads any target cell. -/
def CorrelatedHaving.selectEnvironments (condition : CorrelatedHaving)
    (context : CorrelationContext) (outerEnv : Env)
    (candidates : List Env) : List Env :=
  candidates.filter (condition.keepsEnvironment context outerEnv)

/-- Result of a computation-phase filtered scan. The consumer may terminate on a selected target, exhaust with accumulated state, or abort at the first filter poison. -/
inductive ComputationHavingScanResult (State Result : Type) where
  | exhausted (state : State)
  | terminated (result : Result)
  | poison (cause : FormalCause)
  deriving Repr, DecidableEq

/-- Scan candidates with the runtime iterator's one-kept-candidate lookahead. A holding filter becomes pending; finding its next kept successor happens before the pending target is consumed. Thus a poison while searching for that successor wins over the current target read, while filters after the prefetched successor remain unread if the consumer terminates. -/
def CorrelatedHaving.scanComputationCandidates
    (condition : CorrelatedHaving) (context : CorrelationContext)
    (outerEnv : Env) (consume : State → Env → State ⊕ Result) :
    List Env → Option Env → State → ComputationHavingScanResult State Result
  | [], none, state => .exhausted state
  | [], some pending, state =>
      match consume state pending with
      | .inl next => .exhausted next
      | .inr result => .terminated result
  | candidate :: remaining, pending, state =>
      match condition.evalComputationIn context
          { innerEnv := candidate, outerEnv } with
      | .notTrue =>
          condition.scanComputationCandidates context outerEnv consume
            remaining pending state
      | .poison cause => .poison cause
      | .holds =>
          match pending with
          | none =>
              condition.scanComputationCandidates context outerEnv consume
                remaining (some candidate) state
          | some current =>
              match consume state current with
              | .inr result => .terminated result
              | .inl next =>
                  condition.scanComputationCandidates context outerEnv consume
                    remaining (some candidate) next

/-- Start one computation-phase filtered scan with no prefetched candidate. -/
def CorrelatedHaving.scanComputation (condition : CorrelatedHaving)
    (context : CorrelationContext) (outerEnv : Env)
    (consume : State → Env → State ⊕ Result)
    (candidates : List Env) (initial : State) :
    ComputationHavingScanResult State Result :=
  condition.scanComputationCandidates context outerEnv consume
    candidates none initial

def CorrelatedHavingLeaf.HoldsIn (context : CorrelationContext)
    (frame : CorrelationFrame) : CorrelatedHavingLeaf → Prop
  | .compareNumbers op left right =>
      ∃ leftValue rightValue,
        left.resolveIn context frame = .value leftValue ∧
        right.resolveIn context frame = .value rightValue ∧
        op.holdsRat leftValue rightValue = true
  | .compareRepetitions op left right =>
      ∃ leftRow rightRow,
        frame.rowAt? left = some leftRow ∧
        frame.rowAt? right = some rightRow ∧
        op.holdsRow leftRow rightRow = true

/-- Declarative truth predicate for the correlated filter. Atomic comparisons are stated over resolved values/rows independently of the executable `Bool`; connective structure mirrors the shared tree. -/
def CorrelatedHaving.HoldsIn (condition : CorrelatedHaving)
    (context : CorrelationContext) (frame : CorrelationFrame) : Prop :=
  match condition with
  | .leaf leaf => leaf.HoldsIn context frame
  | .and left right =>
      CorrelatedHaving.HoldsIn left context frame ∧
        CorrelatedHaving.HoldsIn right context frame
  | .or left right =>
      CorrelatedHaving.HoldsIn left context frame ∨
        CorrelatedHaving.HoldsIn right context frame

/-- One-group executable wrapper retained for the established public capsule. -/
def CorrelatedHaving.evalTruth (context : SingleGroupValidationContext)
    (frame : SingleGroupFilterFrame) (condition : CorrelatedHaving) : K :=
  condition.evalTruthIn context.asCorrelationContext (frame.toCorrelationFrame context)

/-- One-group declarative wrapper retained for the established proof boundary. -/
def CorrelatedHaving.Holds (context : SingleGroupValidationContext)
    (frame : SingleGroupFilterFrame) (condition : CorrelatedHaving) : Prop :=
  condition.HoldsIn context.asCorrelationContext (frame.toCorrelationFrame context)

structure SingleCorrelatedStar where
  valueField : FlatNumberField
  having : OriginCheckedCorrelatedHaving

def SingleCorrelatedStar.keeps (star : SingleCorrelatedStar)
    (context : CapturedSingleGroupContext) (innerRow : RowIndex) : Bool :=
  star.having.condition.keepsEnvironment context.rows.asCorrelationContext
    (context.rows.envAt context.outerRow) (context.rows.envAt innerRow)

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
