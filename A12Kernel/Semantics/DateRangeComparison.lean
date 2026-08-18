import A12Kernel.Semantics.DateRangeOverlap
import A12Kernel.Semantics.ScalarEquality

/-! # Resolved DateRange construction equality

This capsule compares filled, already-resolved full-Date constructions with one another or with one stored DateRange while retaining the mixed pair's authored positions. It owns only exact equality and inequality. Empty and formally unavailable input, checked field/path authoring, endpoint format admission and fragment completion, raw parsing, computation targets and rendering, overlap arguments, and bound extraction remain separate.
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
