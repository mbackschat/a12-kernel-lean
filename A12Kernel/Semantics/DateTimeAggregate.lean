import A12Kernel.Semantics.DateAggregate
import A12Kernel.Semantics.DateTimeComparison

/-! # Resolved DateTime instant extrema

This capsule applies the shared temporal extremum fold to already-classified whole-second DateTime instants. Selection follows physical instant chronology, never local wall-label order. Operand expansion, formats, parsing, zone resolution, checked lowering, computation targets, and subsecond values remain outside.
-/

namespace A12Kernel

namespace TemporalExtremumOp

/-- Select one resolved instant, preserving the left value on an exact tie. -/
def selectInstant (op : TemporalExtremumOp) (left right : Instant) : Instant :=
  match op with
  | .minimum =>
      if TemporalComparisonOp.before.holdsInstant right left then right else left
  | .maximum =>
      if TemporalComparisonOp.before.holdsInstant left right then right else left

end TemporalExtremumOp

/-- One already-expanded DateTime instant aggregate side. -/
abbrev ResolvedDateTimeAggregateSide := ResolvedTemporalAggregateSide Instant

/-- Evaluate one resolved DateTime extremum as the shared classified comparison operand. -/
def evalDateTimeExtremumAggregate (op : TemporalExtremumOp)
    (side : ResolvedDateTimeAggregateSide) : SimpleComparisonOperand Instant :=
  evalTemporalExtremumAggregate op.selectInstant side

end A12Kernel
