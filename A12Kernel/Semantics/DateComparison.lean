import A12Kernel.Semantics.FullDate
import A12Kernel.Semantics.ScalarEquality

/-! # Resolved full-Date comparison

This capsule evaluates the six ordinary comparison operators after both operands have been classified as admitted full Dates, no value, or formally unavailable. It compares present values by calendar identity and chronology rather than stored text, and it retains symmetric missing provenance for validation polarity. Literal typing and parsing, DateTime instant comparison, checked lowering, and raw cells remain outside.
-/

namespace A12Kernel

/-- The complete comparison family accepted for two resolved Date values. -/
inductive DateComparisonOp where
  | equal
  | notEqual
  | before
  | beforeOrEqual
  | after
  | afterOrEqual
  deriving Repr, DecidableEq

/-- Operator obtained when the two authored operands exchange positions. -/
def DateComparisonOp.swapped : DateComparisonOp → DateComparisonOp
  | .equal => .equal
  | .notEqual => .notEqual
  | .before => .after
  | .beforeOrEqual => .afterOrEqual
  | .after => .before
  | .afterOrEqual => .beforeOrEqual

/-- Evaluate one comparison over two present full-Date values. -/
def DateComparisonOp.holds (op : DateComparisonOp)
    (left right : FullDate) : Bool :=
  match op with
  | .equal => left == right
  | .notEqual => left != right
  | .before => left.before right
  | .beforeOrEqual => !right.before left
  | .after => right.before left
  | .afterOrEqual => !left.before right

/-- Evaluate two classified Date operands. Formal unavailability dominates no value; a no-value operand makes comparison not fire; and a true comparison is omission-typed exactly when either present result retains missing provenance. -/
def DateComparisonOp.eval (op : DateComparisonOp)
    (leftOperand rightOperand : SimpleComparisonOperand FullDate) : Verdict :=
  match leftOperand, rightOperand with
  | .unknown _, _ | _, .unknown _ => .unknown
  | .notEvaluated, _ | _, .notEvaluated => .notFired
  | .value left leftGiven, .value right rightGiven =>
      if op.holds left right then
        if leftGiven && rightGiven then .fired .value else .fired .omission
      else
        .notFired

end A12Kernel
