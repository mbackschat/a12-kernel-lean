import A12Kernel.Semantics.StringCascade

/-! # A12Kernel.Semantics.StringAlternatives — one resolved String alternative table

This capsule implements the resolved runtime boundary of [`spec/09-computations.md` §5](../../spec/09-computations.md#5-where-a-computation-runs--scope-and-the-parallel-join) by composing the existing operation-neutral first-match selector with one already-resolved nonrepeatable String target. An optional common precondition lowers by left-conjoining it to each guarded alternative before that same selector runs. Selection completes before the chosen expression is evaluated: no match is clean no-value, selection poison is target poison, and a selected expression is evaluated exactly once without outcome-driven fallback.

The caller supplies a model-legal guarded table and an already-resolved common condition when present. Empty lists are totalized but not claimed authorable. Unguarded-singleton lowering, model checks, paths, repeats, scheduling, multiple computations per target, and generated validation remain separate.
-/

namespace A12Kernel

/-- One resolved guarded String alternative table and its shared target state. Target and prior state are not duplicated in each alternative. -/
structure StringAlternativeComputation where
  targetField : FieldId
  alternatives : List (ComputationAlternative StringExpr)
  targetPolicy : StringFieldPolicy
  prior : PriorStringTarget
  deriving Repr, DecidableEq

namespace StringAlternativeComputation

/-- Lower an optional whole-computation precondition by left-conjoining it to every already-guarded alternative. The returned table stays in the existing first-match core. -/
def withCommonPrecondition (computation : StringAlternativeComputation)
    (commonPrecondition : Option ComputationCondition) :
    StringAlternativeComputation :=
  { computation with
    alternatives := (ComputationAlternative.expandCommonPrecondition
      commonPrecondition computation.alternatives) }

/-- Materialize the already-selected expression as the existing one-step String computation. This function never performs selection. -/
def selectedStep (computation : StringAlternativeComputation)
    (expression : StringExpr) : StringComputationStep where
  targetField := computation.targetField
  expression
  targetPolicy := computation.targetPolicy
  prior := computation.prior

/-- Select once, then evaluate only the selected expression. An operation outcome is never fed back into the alternative scan. -/
def evaluateOutcome (computation : StringAlternativeComputation)
    (context : StringComputationContext) :
    Except StringComputationFault StringTargetOutcome :=
  match ComputationAlternative.selectFirst computation.alternatives context with
  | .noMatch => .ok .noValue
  | .poison cause => .ok (.poison cause)
  | .selected expression => (computation.selectedStep expression).evaluateOutcome context

/-- Evaluate the resolved table through the shared target check and existing change-only delta projection without mutating a document. -/
def evaluate (computation : StringAlternativeComputation)
    (context : StringComputationContext) :
    Except StringComputationFault StringComputationStepResult :=
  match computation.evaluateOutcome context with
  | .error fault => .error fault
  | .ok outcome => .ok {
      outcome
      delta := outcome.projectDelta computation.prior }

end StringAlternativeComputation

end A12Kernel
