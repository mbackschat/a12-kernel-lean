import A12Kernel.Semantics.FullDate
import A12Kernel.Semantics.ScalarEquality
import A12Kernel.Semantics.DateTimeComparison

/-! # Resolved temporal comparison operations and full-Date comparison

This capsule evaluates the shared six ordinary temporal comparison operators after both operands have been classified as admitted full Dates, no value, or formally unavailable. It compares present values by calendar identity and chronology rather than stored text, and it retains symmetric missing provenance for validation polarity. Typed validation observations delegate to that same classified path; literal typing, parsing, raw-cell checking, and declaration/path lowering remain outside.
-/

namespace A12Kernel

/-- Evaluate one comparison over two present full-Date values. -/
def TemporalComparisonOp.holds (op : TemporalComparisonOp)
    (left right : FullDate) : Bool :=
  match op with
  | .equal => left == right
  | .notEqual => left != right
  | .before => left.before right
  | .beforeOrEqual => !right.before left
  | .after => right.before left
  | .afterOrEqual => !left.before right

/-- Evaluate two classified Date operands through the shared symmetric scalar projection. -/
def TemporalComparisonOp.eval (op : TemporalComparisonOp)
    (leftOperand rightOperand : SimpleComparisonOperand FullDate) : Verdict :=
  evalSymmetricComparison op.holds leftOperand rightOperand

/-- Evaluate two typed full-Date validation observations through the already-classified comparison path. -/
def TemporalComparisonOp.evalObserved (op : TemporalComparisonOp)
    (left right : CellObservation FullDate) : Verdict :=
  op.eval left.asValidationSimpleOperand right.asValidationSimpleOperand

end A12Kernel
