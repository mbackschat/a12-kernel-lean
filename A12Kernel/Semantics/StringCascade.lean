import A12Kernel.Semantics.StringComputation

/-! # A12Kernel.Semantics.StringCascade — one explicit String dependency edge

This capsule composes exactly two already-resolved String computation steps. The producer's checked outcome, not its observable delta or applied document state, becomes the consumer's dependency read. The construction is deliberately not a dependency graph or scheduling semantics.
-/

namespace A12Kernel

/-- A target error is formal invalidity when a later computation reads that target. The attempted payload is intentionally not carried into the dependency cell. -/
def StringTargetError.dependencyCause : StringTargetError → FormalCause
  | .lineBreak | .tooShort | .tooLong => .declaredConstraint

/-- A validation-scoped required finding cannot represent computation poison because computation reads deliberately ignore that finding. -/
inductive StringDependencyFault where
  | validationScopedRequired
  deriving Repr, DecidableEq

/-- A checked synthetic dependency cell together with the same representation invariant required of document cells. This is an evaluation overlay, not an applied document state. -/
structure StringDependencyCell where
  checked : CheckedCell
  wellFormed : checked.WellFormed

namespace StringDependencyCell

def empty : StringDependencyCell := {
  checked := { rawPresent := false, parsed := none, findings := [] }
  wellFormed := by simp [CheckedCell.WellFormed] }

def value (stored : StoredString) : StringDependencyCell := {
  checked := {
    rawPresent := true
    parsed := some (.str stored.text)
    findings := [] }
  wellFormed := by simp [CheckedCell.WellFormed] }

def poison (cause : FormalCause) : StringDependencyCell := {
  checked := {
    rawPresent := true
    parsed := none
    findings := [cause] }
  wellFormed := by simp [CheckedCell.WellFormed] }

/-- Convert one completed target outcome into the cell observed by an explicitly later dependent computation. Accepted values are visible, clean no-value is empty, and target rejection or inherited formal invalidity is poison. -/
def ofOutcome : StringTargetOutcome → Except StringDependencyFault StringDependencyCell
  | .noValue => pure empty
  | .accepted stored => pure (value stored)
  | .errored _ cause => pure (poison cause.dependencyCause)
  | .poison .required =>
      throw .validationScopedRequired
  | .poison cause => pure (poison cause)

end StringDependencyCell

namespace StringComputationContext

/-- Overlay one already-validated dependency cell at exactly one field. -/
def withDependencyCell (context : StringComputationContext) (field : FieldId)
    (dependency : StringDependencyCell) : StringComputationContext where
  read candidate :=
    if candidate == field then dependency.checked else context.read candidate

/-- Shadow exactly one document read with a completed producer outcome. Other fields continue to read from the original context. -/
def withDependencyOutcome (context : StringComputationContext) (field : FieldId)
    (outcome : StringTargetOutcome) :
    Except StringDependencyFault StringComputationContext :=
  match StringDependencyCell.ofOutcome outcome with
  | .ok dependency => .ok (context.withDependencyCell field dependency)
  | .error fault => .error fault

end StringComputationContext

/-- One already-resolved computation step in an explicitly ordered two-step cascade. -/
structure StringComputationStep where
  targetField : FieldId
  expression : StringExpr
  targetPolicy : StringFieldPolicy
  prior : PriorStringTarget
  deriving Repr, DecidableEq

/-- Internal result needed by a later dependent step and by the observable delta projection. -/
structure StringComputationStepResult where
  outcome : StringTargetOutcome
  delta : Option StringDelta
  deriving Repr, DecidableEq

namespace StringComputationStep

/-- Evaluate through declaration-owned target checking without consulting prior target state. This is the semantic result supplied to a later dependency edge. -/
def evaluateOutcome (step : StringComputationStep) (context : StringComputationContext) :
    Except StringComputationFault StringTargetOutcome :=
  match step.expression.evaluate context with
  | .error fault => .error fault
  | .ok store => .ok (step.targetPolicy.checkTarget store)

/-- Consume an already-evaluated computation condition before the body. Clean not-true yields quiet no-value, while poison is preserved as an invalid target outcome; both return before the body can read an operand. -/
def evaluateOutcomeWhen (step : StringComputationStep)
    (conditionResult : ComputationConditionResult)
    (context : StringComputationContext) :
    Except StringComputationFault StringTargetOutcome :=
  match conditionResult with
  | .notTrue => .ok .noValue
  | .holds => step.evaluateOutcome context
  | .poison cause => .ok (.poison cause)

/-- Evaluate, store, target-check, and project one explicit step without mutating a document. -/
def evaluate (step : StringComputationStep) (context : StringComputationContext) :
    Except StringComputationFault StringComputationStepResult :=
  match step.evaluateOutcome context with
  | .error fault => .error fault
  | .ok outcome => .ok {
      outcome
      delta := outcome.projectDelta step.prior }

end StringComputationStep

/-- Exactly one producer step followed by one consumer step whose context is overlaid at the producer target. -/
structure StringDirectCascade where
  producer : StringComputationStep
  consumer : StringComputationStep
  deriving Repr, DecidableEq

structure StringDirectCascadeResult where
  producer : StringComputationStepResult
  consumer : StringComputationStepResult
  deriving Repr, DecidableEq

inductive StringDirectCascadeFault where
  | producer (fault : StringComputationFault)
  | dependency (fault : StringDependencyFault)
  | consumer (fault : StringComputationFault)
  deriving Repr, DecidableEq

namespace StringDirectCascade

/-- Run the named producer first, shadow its target with the semantic outcome, and then run the named consumer. No result collection order or general scheduling claim is implied. -/
def evaluate (cascade : StringDirectCascade) (context : StringComputationContext) :
    Except StringDirectCascadeFault StringDirectCascadeResult := do
  let producer ← match cascade.producer.evaluate context with
    | .ok result => pure result
    | .error fault => throw (.producer fault)
  let consumerContext ← match context.withDependencyOutcome
      cascade.producer.targetField producer.outcome with
    | .ok context => pure context
    | .error fault => throw (.dependency fault)
  let consumer ← match cascade.consumer.evaluate consumerContext with
    | .ok result => pure result
    | .error fault => throw (.consumer fault)
  pure { producer, consumer }

end StringDirectCascade

end A12Kernel
