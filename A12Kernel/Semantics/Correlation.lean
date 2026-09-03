import A12Kernel.Semantics.Condition
import A12Kernel.Semantics.Iteration

/-! # A12Kernel.Semantics.Correlation — captured outer `$` inside Having

This filter core gives `$` its direct nested-loop meaning through explicit candidate and
captured repetition environments. Reference origins exist only in this filter AST:
ordinary references read the candidate environment and `$` references read the explicitly
captured outer rule environment. Validation and computation consumers select their own
observation phase. The established one-group API remains an adapter over this shared core.
-/

namespace A12Kernel

/-- Origin of one reference inside a correlated `Having` condition. -/
inductive HavingOrigin where
  | inner
  | outer
  deriving Repr, DecidableEq

/-- Resolve exactly one positive binding for a repeatable level. Missing, duplicate, and zero bindings fail closed; correlation must never guess a first row or substitute row zero. -/
def Env.uniqueRowAt? (env : Env) (level : RepeatableLevel) : Option RowIndex :=
  (env.bindingAt level).toOption

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

/-- A String filter reference. Its own kind is carried here rather than being widened out of the
    numeric reference, because the two resolve through different operand domains. -/
structure HavingStringRef where
  origin : HavingOrigin
  field : FlatStringField
  deriving Repr, DecidableEq

/-- A presence filter reference. Presence reads only whether a cell carries a value, so it is
    kind-neutral and needs the field id alone rather than a typed field. -/
structure HavingPresenceRef where
  origin : HavingOrigin
  field : FieldId
  deriving Repr, DecidableEq

/-- Which presence predicate a filter leaf carries. `FieldNotFilled` is a genuine predicate here
    rather than a negation of the other: only a clean empty cell makes it true, so both polarities
    are non-true on a formally unavailable cell. -/
inductive HavingPresencePolarity where
  | filled
  | notFilled
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
  /-- A String field against a literal. The operator is an `EqualityOp` rather than the wider
      comparison type because the kernel refuses a String field in a numeric ordering comparison,
      so the exclusion is carried by this type instead of by a runtime check. -/
  | compareStringLiteral (op : EqualityOp) (reference : HavingStringRef)
      (expected : String)
  /-- `FieldFilled` or `FieldNotFilled` on any declared field. The kernel admits both inside a
      filter, the negative one without the iteration-negativity refusal that governs a rule's own
      condition. -/
  | presence (polarity : HavingPresencePolarity) (reference : HavingPresenceRef)
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

def compareStringLiteral (op : EqualityOp) (reference : HavingStringRef)
    (expected : String) : CorrelatedHaving :=
  .leaf (.compareStringLiteral op reference expected)

def presence (polarity : HavingPresencePolarity)
    (reference : HavingPresenceRef) : CorrelatedHaving :=
  .leaf (.presence polarity reference)

/-- Fields read by the filter in first authored occurrence order. Repetition-only leaves contribute no field dependency, and a String leaf contributes its single reference. -/
def fieldIds : CorrelatedHaving → List FieldId
  | .leaf (.compareNumbers _ left right) =>
      [left.field.id, right.field.id].eraseDups
  | .leaf (.compareRepetitions _ _ _) => []
  | .leaf (.compareStringLiteral _ reference _) => [reference.field.id]
  | .leaf (.presence _ reference) => [reference.field]
  | .and left right | .or left right =>
      (fieldIds left ++ fieldIds right).eraseDups

def referencesField (condition : CorrelatedHaving) (field : FieldId) : Bool :=
  condition.fieldIds.contains field

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
  | .compareStringLiteral _ reference _ => reference.origin.isInner
  | .presence _ reference => reference.origin.isInner

private def CorrelatedHavingLeaf.usesOuter : CorrelatedHavingLeaf → Bool
  | .compareNumbers _ left right => left.origin.isOuter || right.origin.isOuter
  | .compareRepetitions _ left right => left.origin.isOuter || right.origin.isOuter
  | .compareStringLiteral _ reference _ => reference.origin.isOuter
  | .presence _ reference => reference.origin.isOuter

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

/-- The addressed counterpart of `CorrelationContext`. It preserves caller-owned field-read failures and maps invalid repetition bindings into that same structural channel. -/
structure ResolvingCorrelationContext (Error : Type) where
  read : Env → FieldId → Except Error CheckedCell
  bindingError : EnvBindingError → Error

/-- Resolve one numeric filter reference through the selected environment and caller-selected phase. Empty-to-zero is local to numeric comparison; formal invalidity retains its cause for the consuming phase projection. -/
def HavingNumberRef.resolveInAt (reference : HavingNumberRef) (phase : Phase)
    (context : CorrelationContext) (frame : CorrelationFrame) :
    CorrelatedNumberOperand :=
  let rowContext : FlatContext :=
    { read := context.read (frame.envAt reference.origin) }
  match rowContext.resolveNumberComparisonOperandAt phase reference.field with
  | .value amount _ => .value amount
  | .unknown cause => .unknown cause

/-- Resolve the same numeric reference without collapsing a structural addressed-read failure into a formal cell observation. -/
def HavingNumberRef.resolveInAtResolving (reference : HavingNumberRef)
    (phase : Phase) (context : ResolvingCorrelationContext Error)
    (frame : CorrelationFrame) : Except Error CorrelatedNumberOperand := do
  let cell ← context.read (frame.envAt reference.origin) reference.field.id
  let rowContext : FlatContext := { read := fun _ => cell }
  pure (match rowContext.resolveNumberComparisonOperandAt phase reference.field with
    | .value amount _ => .value amount
    | .unknown cause => .unknown cause)

/-- Resolve one String filter reference through the selected environment and phase. There are no
    empty String values, so an absent and a present-empty cell both arrive as `notEvaluated` and
    neither can satisfy an equality; formal invalidity keeps its cause. -/
def HavingStringRef.resolveInAt (reference : HavingStringRef) (phase : Phase)
    (context : CorrelationContext) (frame : CorrelationFrame) :
    SimpleComparisonOperand String :=
  let rowContext : FlatContext :=
    { read := context.read (frame.envAt reference.origin) }
  rowContext.resolveStringComparisonOperandAt phase reference.field

/-- Resolve the same String reference without collapsing a structural addressed-read failure into a formal cell observation. -/
def HavingStringRef.resolveInAtResolving (reference : HavingStringRef)
    (phase : Phase) (context : ResolvingCorrelationContext Error)
    (frame : CorrelationFrame) :
    Except Error (SimpleComparisonOperand String) := do
  let cell ← context.read (frame.envAt reference.origin) reference.field.id
  let rowContext : FlatContext := { read := fun _ => cell }
  pure (rowContext.resolveStringComparisonOperandAt phase reference.field)

/-- Observe one presence reference's cell at a chosen phase. Presence needs the observation itself,
    not a comparison operand, so it reads the phase view directly. -/
def HavingPresenceRef.observeInAt (reference : HavingPresenceRef) (phase : Phase)
    (context : CorrelationContext) (frame : CorrelationFrame) : CellObservation :=
  let rowContext : FlatContext :=
    { read := context.read (frame.envAt reference.origin) }
  rowContext.observeAt phase reference.field

/-- Observe the same presence reference without collapsing a structural addressed-read failure. -/
def HavingPresenceRef.observeInAtResolving (reference : HavingPresenceRef)
    (phase : Phase) (context : ResolvingCorrelationContext Error)
    (frame : CorrelationFrame) : Except Error CellObservation := do
  let cell ← context.read (frame.envAt reference.origin) reference.field
  pure (observeCell phase cell)

/-- Both presence polarities delegate to the shared validation observation consumers, so this leaf
    adds no second account of what "filled" means. Neither polarity fires on a formally unavailable
    cell, which is why they are complements only over clean cells. -/
def HavingPresencePolarity.evalObservation :
    HavingPresencePolarity → CellObservation → Verdict
  | .filled => CellObservation.evalValidationFilled
  | .notFilled => CellObservation.evalValidationNotFilled

/-- Project a shared verdict-producing evaluator into the filter's truth domain. Both the String
    equality and the presence leaves route through here, which keeps their empty-operand and
    formal-unavailability rules owned by the ordinary consumers instead of restated. The filter's
    **selector** keeps only `tru`, so it cannot distinguish the `fls` this yields for a clean
    non-match from `unknown`. That is a property of the selector, not of this projection: filter
    truth is exposed directly through `CorrelatedHaving.evalTruth`, where the two are separable and
    a retained case asserts `unknown` on a malformed operand. So the distinction is preserved here
    rather than collapsed, and only row selection is blind to it. -/
def CorrelatedHavingLeaf.verdictTruth : Verdict → K
  | .fired _ => .tru
  | .notFired => .fls
  | .unknown => .unknown

/-- Resolve one repetition reference through the structural addressed channel. -/
def CorrelationFrame.rowAtResolving (frame : CorrelationFrame)
    (context : ResolvingCorrelationContext Error)
    (reference : HavingRepetitionRef) : Except Error RowIndex :=
  (frame.envAt reference.origin).bindingAt reference.level
    |>.mapError context.bindingError

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
  | .compareStringLiteral op reference expected =>
      CorrelatedHavingLeaf.verdictTruth
        ((reference.resolveInAt .validation context frame).evalDirectString op expected)
  | .presence polarity reference =>
      CorrelatedHavingLeaf.verdictTruth
        (polarity.evalObservation (reference.observeInAt .validation context frame))

/-- Truth of a correlated filter. Numeric empty operands use the comparison-local zero substitution; invalid operands are unknown; only the later selector decides that unknown is not kept. Connectives use the shared strong-Kleene tree evaluator. -/
def CorrelatedHaving.evalTruthIn (condition : CorrelatedHaving)
    (context : CorrelationContext) (frame : CorrelationFrame) : K :=
  condition.evalK (CorrelatedHavingLeaf.evalTruthIn context frame)

/-- Validation filter evaluation over an addressed reader. Strong-Kleene connectives retain both structural read footprints while ordinary formal invalidity remains semantic UNKNOWN. -/
def CorrelatedHavingLeaf.evalTruthInResolving
    (context : ResolvingCorrelationContext Error)
    (frame : CorrelationFrame) : CorrelatedHavingLeaf → Except Error K
  | .compareNumbers op left right => do
      pure (op.evalOperands
        (← left.resolveInAtResolving .validation context frame)
        (← right.resolveInAtResolving .validation context frame))
  | .compareRepetitions op left right => do
      pure (op.evalRows
        (some (← frame.rowAtResolving context left))
        (some (← frame.rowAtResolving context right)))
  | .compareStringLiteral op reference expected => do
      pure (CorrelatedHavingLeaf.verdictTruth
        ((← reference.resolveInAtResolving .validation context frame).evalDirectString
          op expected))
  | .presence polarity reference => do
      pure (CorrelatedHavingLeaf.verdictTruth
        (polarity.evalObservation
          (← reference.observeInAtResolving .validation context frame)))

/-- Evaluate one validation filter tree without converting addressed failure to UNKNOWN. -/
def CorrelatedHaving.evalTruthInResolving (condition : CorrelatedHaving)
    (context : ResolvingCorrelationContext Error)
    (frame : CorrelationFrame) : Except Error K :=
  condition.evalKExcept
    (CorrelatedHavingLeaf.evalTruthInResolving context frame)

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
  | .compareStringLiteral op reference expected =>
      match reference.resolveInAt .computation context frame with
      | .unknown cause => .poison cause
      | .notEvaluated => .notTrue
      | .value actual given =>
          match (SimpleComparisonOperand.value actual given).evalDirectString op expected with
          | .fired _ => .holds
          | _ => .notTrue
  | .presence polarity reference =>
      match reference.observeInAt .computation context frame with
      | .unknown cause | .poison cause => .poison cause
      | observation =>
          match polarity.evalObservation observation with
          | .fired _ => .holds
          | _ => .notTrue

/-- Computation filters reuse the common connective tree but preserve first reached poison instead of validation's unknown-as-drop projection. -/
def CorrelatedHaving.evalComputationIn (condition : CorrelatedHaving)
    (context : CorrelationContext) (frame : CorrelationFrame) :
    ComputationConditionResult :=
  condition.evalComputation
    (CorrelatedHavingLeaf.evalComputationIn context frame)

/-- Computation filter evaluation over an addressed reader. Structural failures are distinct from poison, while numeric poison and connective short-circuiting retain their established order. -/
def CorrelatedHavingLeaf.evalComputationInResolving
    (context : ResolvingCorrelationContext Error)
    (frame : CorrelationFrame) : CorrelatedHavingLeaf →
      Except Error ComputationConditionResult
  | .compareNumbers op left right => do
      match ← left.resolveInAtResolving .computation context frame with
      | .unknown cause => pure (.poison cause)
      | .value leftValue =>
          match ← right.resolveInAtResolving .computation context frame with
          | .unknown cause => pure (.poison cause)
          | .value rightValue =>
              pure (if op.holdsRat leftValue rightValue then .holds else .notTrue)
  | .compareRepetitions op left right => do
      let leftRow ← frame.rowAtResolving context left
      let rightRow ← frame.rowAtResolving context right
      pure (if op.holdsRow leftRow rightRow then .holds else .notTrue)
  | .compareStringLiteral op reference expected => do
      match ← reference.resolveInAtResolving .computation context frame with
      | .unknown cause => pure (.poison cause)
      | .notEvaluated => pure .notTrue
      | .value actual given =>
          pure (match
              (SimpleComparisonOperand.value actual given).evalDirectString op expected with
            | .fired _ => .holds
            | _ => .notTrue)
  | .presence polarity reference => do
      match ← reference.observeInAtResolving .computation context frame with
      | .unknown cause | .poison cause => pure (.poison cause)
      | observation =>
          pure (match polarity.evalObservation observation with
            | .fired _ => .holds
            | _ => .notTrue)

/-- Evaluate one computation filter tree without converting addressed failure to poison or clean non-holding. -/
def CorrelatedHaving.evalComputationInResolving
    (condition : CorrelatedHaving)
    (context : ResolvingCorrelationContext Error)
    (frame : CorrelationFrame) :
      Except Error ComputationConditionResult :=
  condition.evalComputationExcept
    (CorrelatedHavingLeaf.evalComputationInResolving context frame)

/-- Keep one already-resolved candidate environment exactly when the filter is known true. The candidate and captured environments remain separate full repetition identities; false and UNKNOWN both drop the candidate. -/
def CorrelatedHaving.keepsEnvironment (condition : CorrelatedHaving)
    (context : CorrelationContext) (outerEnv innerEnv : Env) : Bool :=
  condition.evalTruthIn context { innerEnv, outerEnv } == .tru

/-- Select resolved candidate environments in their supplied semantic order before a consumer reads any target cell. -/
def CorrelatedHaving.selectEnvironments (condition : CorrelatedHaving)
    (context : CorrelationContext) (outerEnv : Env)
    (candidates : List Env) : List Env :=
  candidates.filter (condition.keepsEnvironment context outerEnv)

/-- Select validation candidates in encounter order while preserving every reached addressed failure outside semantic UNKNOWN. Unlike computation, validation evaluates every candidate before the target consumer starts. -/
def CorrelatedHaving.selectEnvironmentsResolving
    (condition : CorrelatedHaving)
    (context : ResolvingCorrelationContext Error) (outerEnv : Env) :
    List Env → Except Error (List Env)
  | [] => pure []
  | candidate :: remaining => do
      let truth ← condition.evalTruthInResolving context
        { innerEnv := candidate, outerEnv }
      let selected ←
        condition.selectEnvironmentsResolving context outerEnv remaining
      pure (if truth == .tru then candidate :: selected else selected)

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

/-- Addressed computation scan with the established one-kept-successor order. Structural failures from either a reached filter or target consumer remain outside formal poison, and a terminal target still hides filters after its prefetched successor. -/
def CorrelatedHaving.scanComputationCandidatesResolving
    (condition : CorrelatedHaving)
    (context : ResolvingCorrelationContext Error) (outerEnv : Env)
    (consume : State → Env → Except Error (State ⊕ Result)) :
    List Env → Option Env → State →
      Except Error (ComputationHavingScanResult State Result)
  | [], none, state => pure (.exhausted state)
  | [], some pending, state => do
      match ← consume state pending with
      | .inl next => pure (.exhausted next)
      | .inr result => pure (.terminated result)
  | candidate :: remaining, pending, state => do
      match ← condition.evalComputationInResolving context
          { innerEnv := candidate, outerEnv } with
      | .notTrue =>
          condition.scanComputationCandidatesResolving context outerEnv consume
            remaining pending state
      | .poison cause => pure (.poison cause)
      | .holds =>
          match pending with
          | none =>
              condition.scanComputationCandidatesResolving context outerEnv
                consume remaining (some candidate) state
          | some current =>
              match ← consume state current with
              | .inr result => pure (.terminated result)
              | .inl next =>
                  condition.scanComputationCandidatesResolving context outerEnv
                    consume remaining (some candidate) next

/-- Start one addressed computation scan with no prefetched candidate. -/
def CorrelatedHaving.scanComputationResolving
    (condition : CorrelatedHaving)
    (context : ResolvingCorrelationContext Error) (outerEnv : Env)
    (consume : State → Env → Except Error (State ⊕ Result))
    (candidates : List Env) (initial : State) :
    Except Error (ComputationHavingScanResult State Result) :=
  condition.scanComputationCandidatesResolving context outerEnv consume
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
  | .compareStringLiteral op reference expected =>
      ∃ messagePolarity,
        (reference.resolveInAt .validation context frame).evalDirectString op expected
          = .fired messagePolarity
  | .presence polarity reference =>
      ∃ messagePolarity,
        polarity.evalObservation (reference.observeInAt .validation context frame)
          = .fired messagePolarity

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
