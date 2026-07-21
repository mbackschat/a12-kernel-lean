import A12Kernel.Semantics.DateComparison
import A12Kernel.Semantics.DateTime

/-! # Resolved DateTime instant comparison

This capsule evaluates the six ordinary temporal comparison operators after both DateTime operands have resolved to exact epoch-millisecond instants. Comparison observes physical instant identity and order, never the local wall labels that produced them. Typed validation observations delegate to that resolved path. Parsing, zone resolution, raw-cell checking, and declaration/path lowering remain outside.
-/

namespace A12Kernel

/-- Evaluate one comparison over two resolved exact instants. -/
def TemporalComparisonOp.holdsInstant (op : TemporalComparisonOp)
    (left right : Instant) : Bool :=
  match op with
  | .equal => left == right
  | .notEqual => left != right
  | .before => decide (left.epochMillis < right.epochMillis)
  | .beforeOrEqual => decide (left.epochMillis ≤ right.epochMillis)
  | .after => decide (right.epochMillis < left.epochMillis)
  | .afterOrEqual => decide (right.epochMillis ≤ left.epochMillis)

/-- Evaluate two classified resolved DateTime instants through the shared symmetric scalar projection. -/
def TemporalComparisonOp.evalInstant (op : TemporalComparisonOp)
    (leftOperand rightOperand : SimpleComparisonOperand Instant) : Verdict :=
  evalSymmetricComparison op.holdsInstant leftOperand rightOperand

/-- Evaluate two typed exact-instant validation observations through the already-classified comparison path. -/
def TemporalComparisonOp.evalInstantObserved (op : TemporalComparisonOp)
    (left right : CellObservation Instant) : Verdict :=
  op.evalInstant left.asValidationSimpleOperand right.asValidationSimpleOperand

end A12Kernel
