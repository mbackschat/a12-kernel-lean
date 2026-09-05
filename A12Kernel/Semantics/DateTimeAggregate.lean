import A12Kernel.Semantics.DateAggregate
import A12Kernel.Semantics.DateTimeComparison

/-! # Resolved DateTime instant extrema

This capsule applies the shared temporal extremum fold to already-classified exact DateTime instants. Selection follows physical instant chronology, never local wall-label order. Operand expansion, formats, parsing, zone resolution, checked lowering, and computation targets remain outside.
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

namespace CellObservation

/-- Classify one phase-observed cell as an exact-instant DateTime extremum operand.

    The two siblings' rule on this family's payload, with one difference that carries the family's
    whole point: the projected value is the payload's **retained instant**, never an instant
    re-derived from its wall label. A DateTime value holds both, and they disagree wherever a zone
    transition makes one wall label name two moments — so a projection that rebuilt the instant from
    `date` and `time` would order a repeated hour backwards while satisfying every row whose labels
    happen to agree with its instants.

    A payload that is not a DateTime fails closed as malformed rather than being skipped, so a
    broken cell can never read as an unspecified one. -/
def asDateTimeExtremumOperand :
    CellObservation → SimpleComparisonOperand Instant
  | .empty => .notEvaluated
  | .value (.temporal (.dateTime instant _ _ _)) => .value instant true
  | .value _ => .unknown .malformed
  | .unknown cause => .unknown cause
  | .poison cause => .unknown cause

end CellObservation

/-- Evaluate one resolved DateTime extremum as the shared classified comparison operand. -/
def evalDateTimeExtremumAggregate (op : TemporalExtremumOp)
    (side : ResolvedDateTimeAggregateSide) : SimpleComparisonOperand Instant :=
  evalTemporalExtremumAggregate op.selectInstant side

end A12Kernel
