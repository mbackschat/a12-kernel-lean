import A12Kernel.Semantics.FullDate
import A12Kernel.Semantics.ScalarEquality

/-! # Resolved temporal comparison operations and full-Date comparison

This capsule evaluates the six ordinary comparison operators after both operands have been classified as admitted full Dates, no value, or formally unavailable. It compares present values by calendar identity and chronology rather than stored text, and it retains symmetric missing provenance for validation polarity. The operation enum and operand-exchange map are shared by the separate Time and DateTime consumers. Literal typing and parsing, checked lowering, and raw cells remain outside.
-/

namespace A12Kernel

/-- The complete comparison family shared by two comparable resolved temporal values. -/
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

end A12Kernel
