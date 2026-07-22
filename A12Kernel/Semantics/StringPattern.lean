import A12Kernel.Semantics.FlatValidation

/-! # A12Kernel.Semantics.StringPattern — resolved whole-value pattern conditions

This capsule begins after an authored pattern has passed Java compilation and the kernel's additional admission gate. The admitted pattern is injected as a pure whole-value matcher, keeping Java `Pattern` compilation and syntax outside Lean while preserving the validation semantics that consume its result.
-/

namespace A12Kernel

/-- The two admitted String-pattern condition operators. There is no generic condition negation. -/
inductive StringPatternOp where
  | matched
  | violated
  deriving Repr, DecidableEq

namespace StringPatternOp

/-- Whether this operator fires for the matcher's Boolean result. -/
def acceptsMatchResult (op : StringPatternOp) (matchedResult : Bool) : Bool :=
  match op with
  | .matched => matchedResult
  | .violated => !matchedResult

/-- Consume one classified checked String with an already-admitted whole-value matcher. Empty input is not evaluated, formal unavailability remains unknown, and every firing is VALUE-typed because a pattern condition never substitutes for missing input. -/
def evalResolved (op : StringPatternOp) (wholeValueMatches : String → Bool) :
    SimpleComparisonOperand String → Verdict
  | .notEvaluated => .notFired
  | .unknown _ => .unknown
  | .value actual _ =>
      if op.acceptsMatchResult (wholeValueMatches actual) then .fired .value else .notFired

end StringPatternOp

/-- Evaluate a resolved pattern condition through the same normalized validation-phase String read used by direct equality. The matcher is called only for a present, formally valid, nonempty String. -/
def FlatContext.evalResolvedStringPattern (context : FlatContext)
    (op : StringPatternOp) (field : FlatStringField)
    (wholeValueMatches : String → Bool) : Verdict :=
  op.evalResolved wholeValueMatches
    (context.resolveDirectStringComparisonOperand field)

end A12Kernel
