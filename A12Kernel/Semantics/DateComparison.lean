import A12Kernel.Semantics.FullDate

/-! # Resolved full-Date comparison

This capsule evaluates the six ordinary comparison operators after both operands have been decoded as admitted full Dates. It compares calendar identity and chronology rather than stored text. Literal typing and parsing, empty/formal operands, validation polarity, DateTime instant comparison, checked lowering, and cells remain outside.
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

end A12Kernel
