import A12Kernel.Semantics.DateRangeOverlap
import A12Kernel.Semantics.ScalarEquality

/-! # DateRange construction equality

This capsule owns equality and inequality for the shared exact-or-yearless `DateRangeCellValue` domain plus the narrower calendar-level seam for filled resolved full-Date constructions against another construction or one stored range. Checked reads, construction-time label resolution, endpoint format admission and fragment completion, raw parsing, computation targets and rendering, overlap arguments, and bound extraction remain separate.
-/

namespace A12Kernel

/-- One admitted `DateRange(start, finish)` after both full-Date endpoints have resolved. -/
structure ResolvedDateRangeConstruction where
  start : FullDate
  finish : FullDate
  deriving Repr, DecidableEq

namespace ResolvedDateRangeConstruction

/-- Project the construction to the same ordered endpoint carrier used by a stored range. -/
def resolved (construction : ResolvedDateRangeConstruction) :
    ResolvedDateRange :=
  { start := construction.start, finish := construction.finish }

end ResolvedDateRangeConstruction

namespace DateRangeValue

/-- Exact equality of both ordered endpoint instants. Decoded labels and calendar provenance remain available to consumers but do not replace the runtime identity compared by DateRange equality. -/
def sameEndpointInstants (left right : DateRangeValue) : Bool :=
  left.start.instant == right.start.instant &&
    left.finish.instant == right.finish.instant

end DateRangeValue

namespace DateRangeCellValue

/-- Equality of the ordered identity available under one checked DateRange profile. Exact values compare endpoint instants; yearless values compare only the retained ordered components. Distinct profiles are never equal. -/
def sameIdentity : DateRangeCellValue → DateRangeCellValue → Bool
  | .exact left, .exact right => left.sameEndpointInstants right
  | .yearlessMonth leftStart leftFinish,
      .yearlessMonth rightStart rightFinish =>
      leftStart == rightStart && leftFinish == rightFinish
  | .yearlessMonthDay leftStart leftFinish,
      .yearlessMonthDay rightStart rightFinish =>
      leftStart == rightStart && leftFinish == rightFinish
  | _, _ => false

end DateRangeCellValue

/-- Authored side occupied by the construction in the bounded comparison pair. -/
inductive DateRangeConstructionPosition where
  | left
  | right
  deriving Repr, DecidableEq

namespace EqualityOp

/-- Evaluate equality or inequality over the shared exact-or-yearless DateRange identity domain. Empty and formal classification remain owned by the caller-supplied operands. -/
def evalDateRangeCellValues (op : EqualityOp)
    (left right : SimpleComparisonOperand DateRangeCellValue) : Verdict :=
  op.evalSymmetric DateRangeCellValue.sameIdentity left right

private def liftExactDateRangeOperand :
    SimpleComparisonOperand DateRangeValue →
      SimpleComparisonOperand DateRangeCellValue
  | .value value given => .value (.exact value) given
  | .notEvaluated => .notEvaluated
  | .unknown cause => .unknown cause

/-- Evaluate two classified DateRange values by exact ordered endpoint instants. Empty and formal classification remain owned by the caller-supplied operands. -/
def evalDateRangeValues (op : EqualityOp)
    (left right : SimpleComparisonOperand DateRangeValue) : Verdict :=
  op.evalDateRangeCellValues
    (liftExactDateRangeOperand left) (liftExactDateRangeOperand right)

/-- Compare two filled resolved DateRanges by exact ordered endpoint equality or inequality. -/
def evalResolvedDateRanges (op : EqualityOp)
    (left right : ResolvedDateRange) : Verdict :=
  op.evalSymmetric (· == ·)
    (.value left true) (.value right true)

/-- Evaluate exact endpoint equality or inequality between one filled construction and one filled stored range, preserving which side the construction occupied. -/
def evalDateRangeConstruction (op : EqualityOp)
    (position : DateRangeConstructionPosition)
    (construction : ResolvedDateRangeConstruction)
    (stored : ResolvedDateRange) : Verdict :=
  match position with
  | .left => op.evalResolvedDateRanges construction.resolved stored
  | .right => op.evalResolvedDateRanges stored construction.resolved

/-- Evaluate exact endpoint equality or inequality between two filled resolved constructions. -/
def evalDateRangeConstructions (op : EqualityOp)
    (left right : ResolvedDateRangeConstruction) : Verdict :=
  op.evalResolvedDateRanges left.resolved right.resolved

end EqualityOp

end A12Kernel
