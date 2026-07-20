import A12Kernel.Cell

/-! # Shared scalar equality and inequality

This module owns the small comparison seam shared by direct flat scalar validation and resolved Enumeration projection. It models only an already-classified operand, exact caller-supplied equivalence, and VALUE/OMISSION polarity. Consuming clauses remain responsible for their own empty substitution or not-evaluated rule.
-/

namespace A12Kernel

/-- Equality and inequality are separate surface operators; there is no generic condition negation in the language. -/
inductive EqualityOp where
  | equal
  | notEqual
  deriving Repr, DecidableEq

/-- Comparison-local classification for nonnumeric clauses whose substitution polarity is symmetric. Numeric operands use directional fillability instead. -/
inductive SimpleComparisonOperand (α : Type) where
  | value (value : α) (given : Bool)
  | notEvaluated
  | unknown (cause : FormalCause)

private def EqualityOp.holds (op : EqualityOp) (equivalent : Bool) : Bool :=
  match op with
  | .equal => equivalent
  | .notEqual => !equivalent

/-- Evaluate exact equality or inequality after the consuming clause has classified empty and unavailable input. -/
def EqualityOp.evalSimple (op : EqualityOp) (equivalent : α → α → Bool)
    (operand : SimpleComparisonOperand α) (expected : α) : Verdict :=
  match operand with
  | .notEvaluated => .notFired
  | .unknown _ => .unknown
  | .value actual given =>
      if op.holds (equivalent actual expected) then
        if given then .fired .value else .fired .omission
      else
        .notFired

end A12Kernel
