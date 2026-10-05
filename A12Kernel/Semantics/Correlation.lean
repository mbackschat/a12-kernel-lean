import A12Kernel.Semantics.HavingFieldValueList
import A12Kernel.Semantics.CorrelationInputs
import A12Kernel.Semantics.FlatLiteralMembership
import A12Kernel.Semantics.ValidationFillQuantifier
import A12Kernel.Semantics.ComputationFillQuantifier
import A12Kernel.Semantics.FlatComparisonInputs
import A12Kernel.Semantics.Condition
import A12Kernel.Semantics.Iteration
import A12Kernel.Semantics.NumericExpression

/-! # A12Kernel.Semantics.Correlation — captured outer `$` inside Having

This filter core gives `$` its direct nested-loop meaning through explicit candidate and
captured repetition environments. Reference origins exist only in this filter AST:
ordinary references read the candidate environment and `$` references read the explicitly
captured outer rule environment. Validation and computation consumers select their own
observation phase. The established one-group API remains an adapter over this shared core.
-/

namespace A12Kernel

/-- Closed filter-only leaves. An outer reference cannot escape into an ordinary rule expression through this type; connective structure comes from the shared `ConditionTree`. -/
inductive CorrelatedHavingLeaf where
  | numeric (comparison : NumericComparisonOf HavingNumericAtom)
  | simpleComparison (leftOrigin rightOrigin : HavingOrigin) (comparison : FlatComparison)
  /-- A String field against a literal. The operator is an `EqualityOp` rather than the wider
      comparison type because the kernel refuses a String field in a numeric ordering comparison,
      so the exclusion is carried by this type instead of by a runtime check. -/
  | compareStringLiteral (op : EqualityOp) (reference : HavingStringRef)
      (expected : String)
  | fieldMembership (operator : ComputationValueListOperator) (source : HavingFieldValueList)
  | literalMembership (origin : HavingOrigin) (operator : ValueListMembershipOp)
      (source : FlatLiteralMembership)
  | fieldFill (operator : FieldFillQuantifier) (references : List HavingPresenceRef)
  /-- `FieldFilled` or `FieldNotFilled` on any declared field. The kernel admits both inside a
      filter, the negative one without the iteration-negativity refusal that governs a rule's own
      condition. -/
  | presence (polarity : HavingPresencePolarity) (reference : HavingPresenceRef)
  deriving Repr, DecidableEq

/-- Compatibility constructors use the same numeric root as arithmetic and repetition literals. -/
def CorrelatedHavingLeaf.compareNumbers (op : CorrelationComparisonOp)
    (left right : HavingNumberRef) : CorrelatedHavingLeaf :=
  .numeric
    { op := .ordinary op.toNumeric
      left := .atom (.field left)
      right := .atom (.field right) }

def CorrelatedHavingLeaf.compareRepetitions (op : CorrelationComparisonOp)
    (left right : HavingRepetitionRef) : CorrelatedHavingLeaf :=
  .numeric
    { op := .ordinary op.toNumeric
      left := .atom (.repetition left)
      right := .atom (.repetition right) }

def CorrelatedHavingLeaf.compareNumberLiteral (op : CorrelationComparisonOp)
    (reference : HavingNumberRef) (literal : DecodedNumericLiteral) : CorrelatedHavingLeaf :=
  .numeric
    { op := .ordinary op.toNumeric
      left := .atom (.field reference)
      right := .literal literal }

/-- A correlated filter reuses the common connective tree while retaining its environment-sensitive leaf domain. -/
abbrev CorrelatedHaving := ConditionTree CorrelatedHavingLeaf

namespace CorrelatedHaving

def compareNumbers (op : CorrelationComparisonOp)
    (left right : HavingNumberRef) : CorrelatedHaving :=
  .leaf (.compareNumbers op left right)

def compareRepetitions (op : CorrelationComparisonOp)
    (left right : HavingRepetitionRef) : CorrelatedHaving :=
  .leaf (.compareRepetitions op left right)

def compareNumberLiteral (op : CorrelationComparisonOp) (reference : HavingNumberRef)
    (literal : DecodedNumericLiteral) : CorrelatedHaving :=
  .leaf (.compareNumberLiteral op reference literal)

def compareStringLiteral (op : EqualityOp) (reference : HavingStringRef)
    (expected : String) : CorrelatedHaving :=
  .leaf (.compareStringLiteral op reference expected)

def presence (polarity : HavingPresencePolarity)
    (reference : HavingPresenceRef) : CorrelatedHaving :=
  .leaf (.presence polarity reference)

/-- Fields read by the filter in first authored occurrence order. Repetition-only leaves contribute no field dependency, and a String leaf contributes its single reference. -/
def fieldIds : CorrelatedHaving → List FieldId
  | .leaf (.numeric comparison) =>
      ((comparison.left.atoms ++ comparison.right.atoms).filterMap (·.fieldId?)).eraseDups
  | .leaf (.simpleComparison _ _ comparison) => comparison.fields.map (·.id) |>.eraseDups
  | .leaf (.compareStringLiteral _ reference _) => [reference.field.id]
  | .leaf (.literalMembership _ _ source) => [source.field.id]
  | .leaf (.fieldMembership _ source) => source.references.map (·.field) |>.eraseDups
  | .leaf (.fieldFill _ references) => references.map (·.field) |>.eraseDups
  | .leaf (.presence _ reference) => [reference.field]
  | .and left right | .or left right =>
      (fieldIds left ++ fieldIds right).eraseDups

def referencesField (condition : CorrelatedHaving) (field : FieldId) : Bool :=
  condition.fieldIds.contains field

/-- Fields the filter reads through a `$`-marked reference, in first authored occurrence order. The
    Kernel judges a marked read as the rule's own read, so these alone of a body's reads reach the
    rule's error-field gates ([inbound](../../docs/SOURCES.md#inbound-2026-09-26d-reference-set)). -/
def markedFieldIds : CorrelatedHaving → List FieldId
  | .leaf (.numeric comparison) =>
      ((comparison.left.atoms ++ comparison.right.atoms).filter (·.origin? == some .outer)
        |>.filterMap (·.fieldId?)).eraseDups
  | .leaf (.simpleComparison left right comparison) =>
      ((if left == .outer then comparison.inputFields.1 else []) ++
        (if right == .outer then comparison.inputFields.2 else [])).map (·.id) |>.eraseDups
  | .leaf (.compareStringLiteral _ reference _) =>
      if reference.origin == .outer then [reference.field.id] else []
  | .leaf (.literalMembership origin _ source) =>
      if origin == .outer then [source.field.id] else []
  | .leaf (.fieldMembership _ source) =>
      (source.references.filter (·.origin == .outer)).map (·.field) |>.eraseDups
  | .leaf (.fieldFill _ references) =>
      (references.filter (·.origin == .outer)).map (·.field) |>.eraseDups
  | .leaf (.presence _ reference) =>
      if reference.origin == .outer then [reference.field] else []
  | .and left right | .or left right =>
      (markedFieldIds left ++ markedFieldIds right).eraseDups

def referencesMarkedField (condition : CorrelatedHaving) (field : FieldId) : Bool :=
  condition.markedFieldIds.contains field

end CorrelatedHaving

private def HavingOrigin.isInner : HavingOrigin → Bool
  | .inner => true
  | .outer => false

private def HavingOrigin.isOuter : HavingOrigin → Bool
  | .inner => false
  | .outer => true

private def CorrelatedHavingLeaf.usesInner : CorrelatedHavingLeaf → Bool
  | .numeric comparison =>
      comparison.left.anyAtom (·.origin?.any HavingOrigin.isInner) || comparison.right.anyAtom (·.origin?.any HavingOrigin.isInner)
  | .simpleComparison left right comparison =>
      (left.isInner && !comparison.inputFields.1.isEmpty) ||
        (right.isInner && !comparison.inputFields.2.isEmpty)
  | .compareStringLiteral _ reference _ => reference.origin.isInner
  | .literalMembership origin _ _ => origin.isInner
  | .fieldMembership _ source => source.references.any (·.origin.isInner)
  | .fieldFill _ references => references.any (·.origin.isInner)
  | .presence _ reference => reference.origin.isInner

private def CorrelatedHavingLeaf.usesOuter : CorrelatedHavingLeaf → Bool
  | .numeric comparison =>
      comparison.left.anyAtom (·.origin?.any HavingOrigin.isOuter) || comparison.right.anyAtom (·.origin?.any HavingOrigin.isOuter)
  | .simpleComparison left right comparison =>
      (left.isOuter && !comparison.inputFields.1.isEmpty) ||
        (right.isOuter && !comparison.inputFields.2.isEmpty)
  | .compareStringLiteral _ reference _ => reference.origin.isOuter
  | .literalMembership origin _ _ => origin.isOuter
  | .fieldMembership _ source => source.references.any (·.origin.isOuter)
  | .fieldFill _ references => references.any (·.origin.isOuter)
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

def evalHavingFieldFillValidation (operator : FieldFillQuantifier)
    (references : List HavingPresenceRef) (context : CorrelationContext) (frame : CorrelationFrame) : Verdict :=
  Id.run (operator.evalValidationRead (fun ref => pure (ref.observeInAt .validation context frame)) references)

def CorrelatedHavingLeaf.evalTruthIn (context : CorrelationContext)
    (frame : CorrelationFrame) : CorrelatedHavingLeaf → K
  | .numeric comparison =>
      CorrelatedHavingLeaf.verdictTruth
        (comparison.evalWith (HavingNumericAtom.readValidation context frame))
  | .simpleComparison left right comparison =>
      match comparison.evalSimpleValidationReads
          (fun field => Except.ok (ε := Empty) (context.read (frame.envAt left) field))
          (fun field => Except.ok (ε := Empty) (context.read (frame.envAt right) field)) with
      | .ok verdict => CorrelatedHavingLeaf.verdictTruth verdict
      | .error impossible => nomatch impossible
  | .compareStringLiteral op reference expected =>
      CorrelatedHavingLeaf.verdictTruth
        (reference.compareResolved (reference.resolveInAt .validation context frame) op expected)
  | .fieldMembership operator source =>
      CorrelatedHavingLeaf.verdictTruth (source.evalValidation operator (fun origin => context.read (frame.envAt origin)))
  | .literalMembership origin operator source =>
      CorrelatedHavingLeaf.verdictTruth (source.evalValidation operator (context.read (frame.envAt origin) source.field.id))
  | .fieldFill operator references =>
      CorrelatedHavingLeaf.verdictTruth (evalHavingFieldFillValidation operator references context frame)
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
  | .numeric comparison => do
      let left ← comparison.left.mapM (HavingNumericAtom.readValidationResolving context frame)
      let right ← comparison.right.mapM (HavingNumericAtom.readValidationResolving context frame)
      pure (CorrelatedHavingLeaf.verdictTruth
        (({ comparison with left, right } :
          NumericComparisonOf (Except Unit NumericArithmeticOutcome)).evalWith id))
  | .simpleComparison left right comparison => do
      pure (CorrelatedHavingLeaf.verdictTruth (← comparison.evalSimpleValidationReads
        (context.read (frame.envAt left)) (context.read (frame.envAt right))))
  | .compareStringLiteral op reference expected => do
      pure (CorrelatedHavingLeaf.verdictTruth
        (reference.compareResolved (← reference.resolveInAtResolving .validation context frame)
          op expected))
  | .fieldMembership operator source => do
      pure (CorrelatedHavingLeaf.verdictTruth (← source.evalValidationRead operator (fun origin => context.read (frame.envAt origin))))
  | .literalMembership origin operator source => do
      pure (CorrelatedHavingLeaf.verdictTruth (source.evalValidation operator (← context.read (frame.envAt origin) source.field.id)))
  | .fieldFill operator references => do
      pure (CorrelatedHavingLeaf.verdictTruth (← operator.evalValidationRead
        (fun ref => ref.observeInAtResolving .validation context frame) references))
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
  | .numeric comparison =>
      match comparison.evalComputationWith
          (fun atom => Except.ok (ε := Empty) (atom.readComputation context frame)) with
      | .ok result => result
      | .error impossible => nomatch impossible
  | .simpleComparison left right comparison =>
      match comparison.evalSimpleComputationReads
          (fun field => Except.ok (ε := Empty) (context.read (frame.envAt left) field))
          (fun field => Except.ok (ε := Empty) (context.read (frame.envAt right) field)) with
      | .ok result => result
      | .error impossible => nomatch impossible
  | .compareStringLiteral op reference expected =>
      match reference.resolveInAt .computation context frame with
      | .unknown cause => .poison cause
      | .notEvaluated => .notTrue
      | .value actual given =>
          match reference.compareResolved (.value actual given) op expected with
          | .fired _ => .holds
          | _ => .notTrue
  | .fieldMembership operator source =>
      source.evalComputation operator (fun origin => context.read (frame.envAt origin))
  | .literalMembership origin operator source =>
      source.evalComputation operator (context.read (frame.envAt origin) source.field.id)
  | .fieldFill operator references =>
      Id.run (operator.evalComputationRead
        (fun ref => pure (ref.observeInAt .computation context frame).asComputationFillSlot) references)
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
  | .numeric comparison =>
      comparison.evalComputationWith (HavingNumericAtom.readComputationResolving context frame)
  | .simpleComparison left right comparison =>
      comparison.evalSimpleComputationReads
        (context.read (frame.envAt left)) (context.read (frame.envAt right))
  | .compareStringLiteral op reference expected => do
      match ← reference.resolveInAtResolving .computation context frame with
      | .unknown cause => pure (.poison cause)
      | .notEvaluated => pure .notTrue
      | .value actual given =>
          pure (match
              reference.compareResolved (.value actual given) op expected with
            | .fired _ => .holds
            | _ => .notTrue)
  | .fieldMembership operator source =>
      source.evalComputationRead operator (fun origin => context.read (frame.envAt origin))
  | .literalMembership origin operator source => do
      pure (source.evalComputation operator (← context.read (frame.envAt origin) source.field.id))
  | .fieldFill operator references =>
      operator.evalComputationRead (fun ref =>
        CellObservation.asComputationFillSlot <$> ref.observeInAtResolving .computation context frame) references
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
  | .numeric comparison =>
      ∃ left right messagePolarity,
        comparison.left.lowerForEvaluation.evalAdmittedValidation?
          (HavingNumericAtom.readValidation context frame) = some left ∧
        comparison.right.lowerForEvaluation.evalAdmittedValidation?
          (HavingNumericAtom.readValidation context frame) = some right ∧
        comparison.op.evalArithmeticWith left right = .fired messagePolarity
  | .simpleComparison left right comparison =>
      ∃ polarity, comparison.evalSimpleValidationReads
        (fun field => Except.ok (ε := Empty) (context.read (frame.envAt left) field))
        (fun field => Except.ok (ε := Empty) (context.read (frame.envAt right) field)) =
          .ok (.fired polarity)
  | .compareStringLiteral op reference expected =>
      ∃ messagePolarity,
        reference.compareResolved (reference.resolveInAt .validation context frame) op expected
          = .fired messagePolarity
  | .fieldMembership operator source =>
      ∃ polarity, source.evalValidation operator (fun origin => context.read (frame.envAt origin)) = .fired polarity
  | .literalMembership origin operator source =>
      ∃ polarity, source.evalValidation operator (context.read (frame.envAt origin) source.field.id) = .fired polarity
  | .fieldFill operator references =>
      ∃ messagePolarity, evalHavingFieldFillValidation operator references context frame = .fired messagePolarity
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
