import A12Kernel.Semantics.ScalarEquality

/-! # Resolved exact-instant temporal comparison

This capsule owns the shared six-operator temporal dispatch and evaluates operands after they have resolved to exact epoch-millisecond instants. Comparison observes physical instant identity and order, never the local wall labels that produced them. Typed validation observations and the low-level flat temporal consumer delegate to this path. Parsing, zone resolution, format admission, and checked declaration/path lowering remain outside.
-/

namespace A12Kernel

/-- The complete comparison family shared by comparable resolved temporal values. -/
inductive TemporalComparisonOp where
  | equal
  | notEqual
  | before
  | beforeOrEqual
  | after
  | afterOrEqual
  deriving Repr, DecidableEq

/-- Operator obtained when the two authored operands exchange positions. -/
def TemporalComparisonOp.swapped : TemporalComparisonOp → TemporalComparisonOp
  | .equal => .equal
  | .notEqual => .notEqual
  | .before => .after
  | .beforeOrEqual => .afterOrEqual
  | .after => .before
  | .afterOrEqual => .beforeOrEqual

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
