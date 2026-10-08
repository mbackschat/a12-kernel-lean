import A12Kernel.Semantics.StringPattern
import A12Kernel.Semantics.HavingSelectedComparison
import A12Kernel.Semantics.HavingDateValidity
import A12Kernel.Semantics.HavingFieldFill
import A12Kernel.Semantics.HavingUniqueness
import A12Kernel.Semantics.HavingGroupPresence
import A12Kernel.Semantics.HavingTypeValidity
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
  | temporalExpression (comparison : HavingTemporalComparison)
  | selectedComparison (comparison : HavingSelectedComparison)
  | simpleComparison (leftOrigin rightOrigin : HavingOrigin) (comparison : FlatComparison)
  /-- A String field against a literal. The operator is an `EqualityOp` rather than the wider
      comparison type because the kernel refuses a String field in a numeric ordering comparison,
      so the exclusion is carried by this type instead of by a runtime check. -/
  | compareStringLiteral (op : EqualityOp) (reference : HavingStringRef)
      (expected : String)
  | dateValidity (operation : ConstructedDateValidityOp) (source : HavingDateComponents)
  | uniqueness (source : HavingUniqueness)
  | fieldMembership (operator : ComputationValueListOperator) (source : HavingFieldValueList)
  | literalMembership (origin : HavingOrigin) (operator : ValueListMembershipOp)
      (source : FlatLiteralMembership)
  | fieldFill (operator : FieldFillQuantifier) (references : List (HavingFieldListSlot HavingPresenceRef))
  /-- `FieldFilled` or `FieldNotFilled` on any declared field. The kernel admits both inside a
      filter, the negative one without the iteration-negativity refusal that governs a rule's own
      condition. -/
  | presence (polarity : HavingPresencePolarity) (reference : HavingPresenceRef)
  | stringPattern (operation : StringPatternOp) (reference : HavingPresenceRef) (pattern : CompiledStringPattern)
  | typeValidity (operation : CustomFieldValidityOp) (reference : HavingPresenceRef) (name : String)
  | groupPresence (operator : GroupPresenceOperator) (origin : HavingOrigin)
      (source : ComputationGroupOperand)
  | groupFill (operator : GroupFillQuantifier) (first : HavingGroupOperand)
      (rest : List HavingGroupOperand)
  deriving Repr

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
      ((comparison.left.atoms ++ comparison.right.atoms).flatMap (·.fieldOrigins) |>.map (·.2)).eraseDups
  | .leaf (.selectedComparison comparison) => comparison.references.map (·.field) |>.eraseDups
  | .leaf (.temporalExpression comparison) => comparison.references.map (·.fieldId) |>.eraseDups
  | .leaf (.simpleComparison _ _ comparison) => comparison.fields.map (·.id) |>.eraseDups
  | .leaf (.compareStringLiteral _ reference _) => [reference.field.id]
  | .leaf (.literalMembership _ _ source) => [source.field.id]
  | .leaf (.dateValidity _ source) => source.references.map (·.field) |>.eraseDups
  | .leaf (.uniqueness source) => source.references.map (·.field) |>.eraseDups
  | .leaf (.fieldMembership _ source) => source.references.map (·.field) |>.eraseDups
  | .leaf (.fieldFill _ references) => (references.flatMap (·.references)).map (·.field) |>.eraseDups
  | .leaf (.presence _ reference) | .leaf (.typeValidity _ reference _) | .leaf (.stringPattern _ reference _) => [reference.field]
  | .leaf (.groupPresence _ _ source) => source.members.eraseDups
  | .leaf (.groupFill _ first rest) => ((first :: rest).flatMap (·.fieldIds)).eraseDups
  | .and left right | .or left right =>
      (fieldIds left ++ fieldIds right).eraseDups

def referencesField (condition : CorrelatedHaving) (field : FieldId) : Bool :=
  condition.fieldIds.contains field

/-- Fields the filter reads through a `$`-marked reference, in first authored occurrence order. The
    Kernel judges a marked read as the rule's own read, so these alone of a body's reads reach the
    rule's error-field gates ([inbound](../../docs/SOURCES.md#inbound-2026-09-26d-reference-set)). -/
def markedFieldIds : CorrelatedHaving → List FieldId
  | .leaf (.numeric comparison) =>
      ((comparison.left.atoms ++ comparison.right.atoms).flatMap (·.fieldOrigins)
        |>.filter (·.1 == .outer) |>.map (·.2)).eraseDups
  | .leaf (.selectedComparison comparison) =>
      (comparison.references.filter (·.origin == .outer)).map (·.field) |>.eraseDups
  | .leaf (.temporalExpression comparison) =>
      (comparison.references.filter (·.origin == .outer)).map (·.fieldId) |>.eraseDups
  | .leaf (.simpleComparison left right comparison) =>
      ((if left == .outer then comparison.inputFields.1 else []) ++
        (if right == .outer then comparison.inputFields.2 else [])).map (·.id) |>.eraseDups
  | .leaf (.compareStringLiteral _ reference _) =>
      if reference.origin == .outer then [reference.field.id] else []
  | .leaf (.literalMembership origin _ source) =>
      if origin == .outer then [source.field.id] else []
  | .leaf (.dateValidity _ source) =>
      (source.references.filter (·.origin == .outer)).map (·.field) |>.eraseDups
  | .leaf (.uniqueness source) =>
      (source.references.filter (·.origin == .outer)).map (·.field) |>.eraseDups
  | .leaf (.fieldMembership _ source) =>
      (source.references.filter (·.origin == .outer)).map (·.field) |>.eraseDups
  | .leaf (.fieldFill _ references) =>
      ((references.flatMap (·.references)).filter (·.origin == .outer)).map (·.field) |>.eraseDups
  | .leaf (.presence _ reference) | .leaf (.typeValidity _ reference _) | .leaf (.stringPattern _ reference _) =>
      if reference.origin == .outer then [reference.field] else []
  | .leaf (.groupPresence _ origin source) =>
      if origin == .outer then source.members.eraseDups else []
  | .leaf (.groupFill _ first rest) =>
      ((first :: rest).filter (·.origin == .outer) |>.flatMap (·.fieldIds)).eraseDups
  | .and left right | .or left right =>
      (markedFieldIds left ++ markedFieldIds right).eraseDups

def referencesMarkedField (condition : CorrelatedHaving) (field : FieldId) : Bool :=
  condition.markedFieldIds.contains field

/-- Target legality uses the ordinary computation group's positive conditional-presence exemption while `referencesField` retains complete membership (spec/09 §5). -/
def forbidsTarget (condition : CorrelatedHaving) (target : FieldId) : Bool :=
  match condition with
  | .leaf (.groupPresence operator _ source) =>
      ComputationConditionOf.forbidsTargetWith
        (.leaf (.groupPresence operator source) : ComputationConditionOf Empty Empty)
        (fun atom => nomatch atom) (fun predicate => nomatch predicate) target
  | .leaf (.groupFill operator first rest) =>
      (havingGroupFillDependencies operator first rest).forbidsTargetWith
        (fun atom => nomatch atom) (fun predicate => nomatch predicate) target
  | .and left right | .or left right => forbidsTarget left target || forbidsTarget right target
  | leaf => leaf.referencesField target

/-- Conditional group dependencies follow the ordinary producer-protection algebra; direct field reads and ordinary-list groups preserve their unconditional dependency (spec/09 §5). -/
def requiresProducer (condition : CorrelatedHaving) (consumer producer : FieldId)
    (producerProtected : ResolvedGroupReference → Bool) : Bool :=
  match condition with
  | .leaf (.groupPresence operator _ source) =>
      ComputationConditionOf.requiresProducerWith
        (.leaf (.groupPresence operator source) : ComputationConditionOf Empty Empty)
        (fun atom => nomatch atom) (fun predicate => nomatch predicate)
        consumer producer producerProtected
  | .leaf (.groupFill operator first rest) =>
      (havingGroupFillDependencies operator first rest).requiresProducerWith
        (fun atom => nomatch atom) (fun predicate => nomatch predicate)
        consumer producer producerProtected
  | .and left right | .or left right =>
      requiresProducer left consumer producer producerProtected ||
        requiresProducer right consumer producer producerProtected
  | leaf => leaf.referencesField producer

end CorrelatedHaving

private def HavingOrigin.isInner : HavingOrigin → Bool
  | .inner => true
  | .outer => false

private def HavingOrigin.isOuter : HavingOrigin → Bool
  | .inner => false
  | .outer => true

private def CorrelatedHavingLeaf.usesInner : CorrelatedHavingLeaf → Bool
  | .numeric comparison =>
      comparison.left.anyAtom (·.origins.any HavingOrigin.isInner) || comparison.right.anyAtom (·.origins.any HavingOrigin.isInner)
  | .selectedComparison comparison => comparison.references.any (·.origin.isInner)
  | .temporalExpression comparison => comparison.references.any (·.origin.isInner)
  | .simpleComparison left right comparison =>
      (left.isInner && !comparison.inputFields.1.isEmpty) ||
        (right.isInner && !comparison.inputFields.2.isEmpty)
  | .compareStringLiteral _ reference _ => reference.origin.isInner
  | .literalMembership origin _ _ => origin.isInner
  | .dateValidity _ source => source.references.any (·.origin.isInner)
  | .uniqueness source => source.references.any (·.origin.isInner)
  | .fieldMembership _ source => source.references.any (·.origin.isInner)
  | .fieldFill _ references => (references.flatMap (·.references)).any (·.origin.isInner)
  | .presence _ reference | .typeValidity _ reference _ | .stringPattern _ reference _ => reference.origin.isInner
  | .groupPresence _ origin _ => origin.isInner
  | .groupFill _ first rest => (first :: rest).any (·.origin.isInner)

private def CorrelatedHavingLeaf.usesOuter : CorrelatedHavingLeaf → Bool
  | .numeric comparison =>
      comparison.left.anyAtom (·.origins.any HavingOrigin.isOuter) || comparison.right.anyAtom (·.origins.any HavingOrigin.isOuter)
  | .selectedComparison comparison => comparison.references.any (·.origin.isOuter)
  | .temporalExpression comparison => comparison.references.any (·.origin.isOuter)
  | .simpleComparison left right comparison =>
      (left.isOuter && !comparison.inputFields.1.isEmpty) ||
        (right.isOuter && !comparison.inputFields.2.isEmpty)
  | .compareStringLiteral _ reference _ => reference.origin.isOuter
  | .literalMembership origin _ _ => origin.isOuter
  | .dateValidity _ source => source.references.any (·.origin.isOuter)
  | .uniqueness source => source.references.any (·.origin.isOuter)
  | .fieldMembership _ source => source.references.any (·.origin.isOuter)
  | .fieldFill _ references => (references.flatMap (·.references)).any (·.origin.isOuter)
  | .presence _ reference | .typeValidity _ reference _ | .stringPattern _ reference _ => reference.origin.isOuter
  | .groupPresence _ origin _ => origin.isOuter
  | .groupFill _ first rest => (first :: rest).any (·.origin.isOuter)

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
    (references : List (HavingFieldListSlot HavingPresenceRef)) (context : CorrelationContext) (frame : CorrelationFrame) : Verdict :=
  match HavingFieldFill.evalValidationRead operator references context.asResolving frame with
  | .ok verdict => verdict
  | .error _ => .unknown

def CorrelatedHavingLeaf.evalTruthIn (context : CorrelationContext)
    (frame : CorrelationFrame) : CorrelatedHavingLeaf → K
  | .numeric comparison =>
      CorrelatedHavingLeaf.verdictTruth
        (comparison.evalWith (HavingNumericAtom.readValidation context frame))
  | .selectedComparison comparison => match comparison.evalValidationRead context.asResolving frame with
      | .ok verdict => CorrelatedHavingLeaf.verdictTruth verdict
      | .error _ => .unknown
  | .temporalExpression comparison => match comparison.evalValidationRead context.asResolving frame with
      | .ok verdict => CorrelatedHavingLeaf.verdictTruth verdict
      | .error _ => .unknown
  | .simpleComparison left right comparison =>
      match comparison.evalSimpleValidationReads
          (fun field => Except.ok (ε := Empty) (context.read (frame.envAt left) field))
          (fun field => Except.ok (ε := Empty) (context.read (frame.envAt right) field)) context.world with
      | .ok verdict => CorrelatedHavingLeaf.verdictTruth verdict
      | .error impossible => nomatch impossible
  | .compareStringLiteral op reference expected =>
      CorrelatedHavingLeaf.verdictTruth
        (reference.compareResolved (reference.resolveInAt .validation context frame) op expected)
  | .dateValidity operation source =>
      match source.evalValidationRead operation context.asResolving frame with
      | .ok verdict => CorrelatedHavingLeaf.verdictTruth verdict
      | .error _ => .unknown
  | .uniqueness source =>
      match source.evalValidationRead context.asResolving frame with
      | .ok verdict => CorrelatedHavingLeaf.verdictTruth verdict
      | .error _ => .unknown
  | .fieldMembership operator source =>
      CorrelatedHavingLeaf.verdictTruth (source.evalValidation operator context frame)
  | .literalMembership origin operator source =>
      CorrelatedHavingLeaf.verdictTruth (source.evalValidation operator (context.read (frame.envAt origin) source.field.id))
  | .fieldFill operator references =>
      CorrelatedHavingLeaf.verdictTruth (evalHavingFieldFillValidation operator references context frame)
  | .presence polarity reference =>
      CorrelatedHavingLeaf.verdictTruth
        (polarity.evalObservation (reference.observeInAt .validation context frame))
  | .stringPattern operation reference compiled =>
      CorrelatedHavingLeaf.verdictTruth (operation.evalResolved compiled.pattern.wholeValueMatches
        (reference.observeInAt .validation context frame).asStringComparisonOperand)
  | .typeValidity operation reference name =>
      match evalHavingTypeValidityValidation operation reference name context.asResolving frame with
      | .ok verdict => CorrelatedHavingLeaf.verdictTruth verdict
      | .error _ => .unknown
  | .groupPresence operator origin source =>
      match evalHavingGroupPresenceValidation operator origin source context.asResolving frame with
      | .ok verdict => CorrelatedHavingLeaf.verdictTruth verdict
      | .error _ => .unknown
  | .groupFill operator first rest =>
      match evalHavingGroupFillValidation operator first rest context.asResolving frame with
      | .ok verdict => CorrelatedHavingLeaf.verdictTruth verdict
      | .error _ => .unknown

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
  | .selectedComparison comparison => CorrelatedHavingLeaf.verdictTruth <$> comparison.evalValidationRead context frame
  | .temporalExpression comparison => CorrelatedHavingLeaf.verdictTruth <$> comparison.evalValidationRead context frame
  | .simpleComparison left right comparison => do
      pure (CorrelatedHavingLeaf.verdictTruth (← comparison.evalSimpleValidationReads
        (context.read (frame.envAt left)) (context.read (frame.envAt right)) context.world
        (some context.temporalValueFailure)))
  | .compareStringLiteral op reference expected => do
      pure (CorrelatedHavingLeaf.verdictTruth
        (reference.compareResolved (← reference.resolveInAtResolving .validation context frame)
          op expected))
  | .dateValidity operation source => CorrelatedHavingLeaf.verdictTruth <$> source.evalValidationRead operation context frame
  | .uniqueness source => CorrelatedHavingLeaf.verdictTruth <$> source.evalValidationRead context frame
  | .fieldMembership operator source => do
      pure (CorrelatedHavingLeaf.verdictTruth (← source.evalValidationRead operator context frame))
  | .literalMembership origin operator source => do
      pure (CorrelatedHavingLeaf.verdictTruth (source.evalValidation operator (← context.read (frame.envAt origin) source.field.id)))
  | .fieldFill operator references => do
      pure (CorrelatedHavingLeaf.verdictTruth (← HavingFieldFill.evalValidationRead operator references context frame))
  | .presence polarity reference => do
      pure (CorrelatedHavingLeaf.verdictTruth
        (polarity.evalObservation
          (← reference.observeInAtResolving .validation context frame)))
  | .stringPattern operation reference compiled => do
      let observation ← reference.observeInAtResolving .validation context frame
      pure (CorrelatedHavingLeaf.verdictTruth
        (operation.evalResolved compiled.pattern.wholeValueMatches observation.asStringComparisonOperand))
  | .typeValidity operation reference name =>
      CorrelatedHavingLeaf.verdictTruth <$> evalHavingTypeValidityValidation operation reference name context frame
  | .groupPresence operator origin source =>
      CorrelatedHavingLeaf.verdictTruth <$> evalHavingGroupPresenceValidation operator origin source context frame
  | .groupFill operator first rest =>
      CorrelatedHavingLeaf.verdictTruth <$> evalHavingGroupFillValidation operator first rest context frame

/-- Generated filters test each leaf for known truth and short-circuit their Boolean tree
(`CodeGenFilterCondition`, `CompositeCondition.getBooleanCode`, spec/07 §3). -/
def CorrelatedHaving.evalTruthInResolving (condition : CorrelatedHaving)
    (context : ResolvingCorrelationContext Error)
    (frame : CorrelationFrame) : Except Error K :=
  (condition.evalBoolExcept fun leaf => do
    pure ((← leaf.evalTruthInResolving context frame) == .tru)).map fun holds =>
      if holds then .tru else .fls

/-- Computation filter evaluation over an addressed reader. Structural failures are distinct from poison, while numeric poison and connective short-circuiting retain their established order. -/
def CorrelatedHavingLeaf.evalComputationInResolving
    (context : ResolvingCorrelationContext Error)
    (frame : CorrelationFrame) : CorrelatedHavingLeaf →
      Except Error ComputationConditionResult
  | .numeric comparison =>
      comparison.evalComputationWith (HavingNumericAtom.readComputationResolving context frame)
  | .selectedComparison comparison => comparison.evalComputationRead context frame
  | .temporalExpression comparison => comparison.evalComputationRead context frame
  | .simpleComparison left right comparison =>
      comparison.evalSimpleComputationReads
        (context.read (frame.envAt left)) (context.read (frame.envAt right)) context.world
        (some context.temporalValueFailure)
  | .compareStringLiteral op reference expected => do
      match ← reference.resolveInAtResolving .computation context frame with
      | .unknown cause => pure (.poison cause)
      | .notEvaluated => pure .notTrue
      | .value actual given =>
          pure (match
              reference.compareResolved (.value actual given) op expected with
            | .fired _ => .holds
            | _ => .notTrue)
  | .dateValidity operation source => source.evalComputationRead operation context frame
  | .uniqueness source => source.evalRead .computation context frame
  | .fieldMembership operator source =>
      source.evalComputationRead operator context frame
  | .literalMembership origin operator source => do
      pure (source.evalComputation operator (← context.read (frame.envAt origin) source.field.id))
  | .fieldFill operator references =>
      HavingFieldFill.evalComputationRead operator references context frame
  | .presence polarity reference => do
      match ← reference.observeInAtResolving .computation context frame with
      | .unknown cause | .poison cause => pure (.poison cause)
      | observation =>
          pure (match polarity.evalObservation observation with
            | .fired _ => .holds
            | _ => .notTrue)
  | .stringPattern operation reference compiled => do
      let observation ← reference.observeInAtResolving .computation context frame
      pure (operation.evalComputationResolved compiled.pattern.wholeValueMatches observation.asStringComparisonOperand)
  | .typeValidity operation reference name =>
      evalHavingTypeValidityComputation operation reference name context frame
  | .groupPresence operator origin source =>
      evalHavingGroupPresenceComputation operator origin source context frame
  | .groupFill operator first rest =>
      evalHavingGroupFillComputation operator first rest context frame

/-- A pure cell reader does not eliminate calendar support failures. -/
def CorrelatedHavingLeaf.evalComputationIn (context : CorrelationContext)
    (frame : CorrelationFrame) : CorrelatedHavingLeaf → Except CorrelationRuntimeFault ComputationConditionResult
  | .numeric comparison => comparison.evalComputationWith (HavingNumericAtom.readComputationIn context frame)
  | leaf => leaf.evalComputationInResolving context.asResolving frame

/-- The shared effectful tree preserves support faults and computation short-circuiting. -/
def CorrelatedHaving.evalComputationIn (condition : CorrelatedHaving)
    (context : CorrelationContext) (frame : CorrelationFrame) : Except CorrelationRuntimeFault ComputationConditionResult :=
  condition.evalComputationExcept (CorrelatedHavingLeaf.evalComputationIn context frame)

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
    List Env → Option Env → State → Except CorrelationRuntimeFault (ComputationHavingScanResult State Result)
  | [], none, state => pure (.exhausted state)
  | [], some pending, state =>
      match consume state pending with
      | .inl next => pure (.exhausted next)
      | .inr result => pure (.terminated result)
  | candidate :: remaining, pending, state => do
      match ← condition.evalComputationIn context
          { innerEnv := candidate, outerEnv } with
      | .notTrue =>
          condition.scanComputationCandidates context outerEnv consume
            remaining pending state
      | .poison cause => pure (.poison cause)
      | .holds =>
          match pending with
          | none =>
              condition.scanComputationCandidates context outerEnv consume
                remaining (some candidate) state
          | some current =>
              match consume state current with
              | .inr result => pure (.terminated result)
              | .inl next =>
                  condition.scanComputationCandidates context outerEnv consume
                    remaining (some candidate) next

/-- Start one computation-phase filtered scan with no prefetched candidate. -/
def CorrelatedHaving.scanComputation (condition : CorrelatedHaving)
    (context : CorrelationContext) (outerEnv : Env)
    (consume : State → Env → State ⊕ Result)
    (candidates : List Env) (initial : State) :
    Except CorrelationRuntimeFault (ComputationHavingScanResult State Result) :=
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
  | .selectedComparison comparison => ∃ polarity, comparison.evalValidationRead context.asResolving frame = .ok (.fired polarity)
  | .temporalExpression comparison => ∃ polarity, comparison.evalValidationRead context.asResolving frame = .ok (.fired polarity)
  | .simpleComparison left right comparison =>
      ∃ polarity, comparison.evalSimpleValidationReads
        (fun field => Except.ok (ε := Empty) (context.read (frame.envAt left) field))
        (fun field => Except.ok (ε := Empty) (context.read (frame.envAt right) field)) context.world =
          .ok (.fired polarity)
  | .compareStringLiteral op reference expected =>
      ∃ messagePolarity,
        reference.compareResolved (reference.resolveInAt .validation context frame) op expected
          = .fired messagePolarity
  | .dateValidity operation source => ∃ polarity, source.evalValidationRead operation context.asResolving frame = .ok (.fired polarity)
  | .uniqueness source => ∃ polarity, source.evalValidationRead context.asResolving frame = .ok (.fired polarity)
  | .fieldMembership operator source =>
      ∃ polarity, source.evalValidation operator context frame = .fired polarity
  | .literalMembership origin operator source =>
      ∃ polarity, source.evalValidation operator (context.read (frame.envAt origin) source.field.id) = .fired polarity
  | .fieldFill operator references =>
      ∃ messagePolarity, evalHavingFieldFillValidation operator references context frame = .fired messagePolarity
  | .presence polarity reference =>
      ∃ messagePolarity,
        polarity.evalObservation (reference.observeInAt .validation context frame)
          = .fired messagePolarity
  | .stringPattern operation reference compiled =>
      ∃ messagePolarity, operation.evalResolved compiled.pattern.wholeValueMatches
        (reference.observeInAt .validation context frame).asStringComparisonOperand = .fired messagePolarity
  | .typeValidity operation reference name =>
      ∃ messagePolarity, evalHavingTypeValidityValidation operation reference name context.asResolving frame =
        .ok (.fired messagePolarity)
  | .groupPresence operator origin source =>
      ∃ messagePolarity, evalHavingGroupPresenceValidation operator origin source context.asResolving frame =
        .ok (.fired messagePolarity)
  | .groupFill operator first rest =>
      ∃ messagePolarity, evalHavingGroupFillValidation operator first rest context.asResolving frame =
        .ok (.fired messagePolarity)

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
