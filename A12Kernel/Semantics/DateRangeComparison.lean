import A12Kernel.Semantics.DateRangeOverlap
import A12Kernel.Semantics.ScalarEquality

/-! # Resolved DateRange construction equality

This capsule compares one already-resolved full-Date construction with one filled stored DateRange while retaining their authored positions. It owns only exact equality and inequality. Other operand pairings, empty and formally unavailable input, field/path authoring, endpoint format admission and fragment completion, raw parsing, computation targets and rendering, overlap arguments, and bound extraction remain separate.
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

/-- Authored side occupied by the construction in the bounded comparison pair. -/
inductive DateRangeConstructionPosition where
  | left
  | right
  deriving Repr, DecidableEq

namespace EqualityOp

/-- Evaluate exact endpoint equality or inequality between one filled construction and one filled stored range, preserving which side the construction occupied. -/
def evalDateRangeConstruction (op : EqualityOp)
    (position : DateRangeConstructionPosition)
    (construction : ResolvedDateRangeConstruction)
    (stored : ResolvedDateRange) : Verdict :=
  let constructed := SimpleComparisonOperand.value construction.resolved true
  let stored := SimpleComparisonOperand.value stored true
  match position with
  | .left => op.evalSymmetric (· == ·) constructed stored
  | .right => op.evalSymmetric (· == ·) stored constructed

end EqualityOp

end A12Kernel
