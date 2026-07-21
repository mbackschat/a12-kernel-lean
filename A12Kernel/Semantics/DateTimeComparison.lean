import A12Kernel.Semantics.DateComparison
import A12Kernel.Semantics.DateTime

/-! # Resolved DateTime instant comparison

This capsule evaluates the six ordinary temporal comparison operators after both DateTime operands have resolved to exact whole-second instants. Comparison observes physical instant identity and order, never the local wall labels that produced them. Parsing, zone resolution, checked lowering, raw cells, and subsecond values remain outside.
-/

namespace A12Kernel

/-- Evaluate one comparison over two resolved whole-second instants. -/
def TemporalComparisonOp.holdsInstant (op : TemporalComparisonOp)
    (left right : Instant) : Bool :=
  match op with
  | .equal => left == right
  | .notEqual => left != right
  | .before => decide (left.epochSecond < right.epochSecond)
  | .beforeOrEqual => decide (left.epochSecond ≤ right.epochSecond)
  | .after => decide (right.epochSecond < left.epochSecond)
  | .afterOrEqual => decide (right.epochSecond ≤ left.epochSecond)

/-- Evaluate two classified resolved DateTime instants through the shared symmetric scalar projection. -/
def TemporalComparisonOp.evalInstant (op : TemporalComparisonOp)
    (leftOperand rightOperand : SimpleComparisonOperand Instant) : Verdict :=
  evalSymmetricComparison op.holdsInstant leftOperand rightOperand

end A12Kernel
