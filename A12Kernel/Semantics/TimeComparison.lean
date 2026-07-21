import A12Kernel.Semantics.DateComparison
import A12Kernel.Semantics.DateTime

/-! # Resolved time-of-day comparison

This capsule evaluates the six ordinary temporal comparison operators after both time-only operands have been decoded to valid whole-second wall times. Kernel checking requires comparable component sets, and time-only parsing gives every operand the same implicit date and model-zone anchor, so comparison reduces exactly to elapsed seconds since midnight. Typed validation observations delegate to that resolved path. Formats, AM/PM decoding, raw-cell checking, declaration/path lowering, and subsecond values remain outside.
-/

namespace A12Kernel

/-- Evaluate one comparison over two decoded whole-second times of day. -/
def TemporalComparisonOp.holdsTime (op : TemporalComparisonOp)
    (left right : TimeOfDay) : Bool :=
  match op with
  | .equal => left == right
  | .notEqual => left != right
  | .before => decide (left.secondsSinceMidnight < right.secondsSinceMidnight)
  | .beforeOrEqual => decide (left.secondsSinceMidnight ≤ right.secondsSinceMidnight)
  | .after => decide (right.secondsSinceMidnight < left.secondsSinceMidnight)
  | .afterOrEqual => decide (right.secondsSinceMidnight ≤ left.secondsSinceMidnight)

/-- Evaluate two classified time-of-day operands through the shared symmetric scalar projection. -/
def TemporalComparisonOp.evalTime (op : TemporalComparisonOp)
    (leftOperand rightOperand : SimpleComparisonOperand TimeOfDay) : Verdict :=
  evalSymmetricComparison op.holdsTime leftOperand rightOperand

/-- Evaluate two typed time-of-day validation observations through the already-classified comparison path. -/
def TemporalComparisonOp.evalTimeObserved (op : TemporalComparisonOp)
    (left right : CellObservation TimeOfDay) : Verdict :=
  op.evalTime left.asValidationSimpleOperand right.asValidationSimpleOperand

end A12Kernel
