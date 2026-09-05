import A12Kernel.Semantics.DateAggregate
import A12Kernel.Semantics.TimeComparison

/-! # Resolved time-of-day extrema

This capsule applies the shared temporal extremum fold to already-classified valid whole-second times of day. Selection follows the decoded seconds-since-midnight coordinate. Operand expansion, formats, parsing, checked lowering, computation targets, and subsecond values remain outside.
-/

namespace A12Kernel

namespace TemporalExtremumOp

/-- Select one decoded time of day, preserving the left value on an exact tie. -/
def selectTime (op : TemporalExtremumOp)
    (left right : TimeOfDay) : TimeOfDay :=
  match op with
  | .minimum =>
      if TemporalComparisonOp.before.holdsTime right left then right else left
  | .maximum =>
      if TemporalComparisonOp.before.holdsTime left right then right else left

end TemporalExtremumOp

/-- One already-expanded time-of-day aggregate side. -/
abbrev ResolvedTimeAggregateSide := ResolvedTemporalAggregateSide TimeOfDay

namespace CellObservation

/-- Classify one phase-observed cell as a time-of-day extremum operand.

    The Date sibling's rule, on this family's payload: an unspecified operand does not compete, and a
    payload that is not a time — or is one whose decoded parts name no valid whole-second clock — fails
    closed as malformed rather than being skipped, so a broken cell can never read as an absent one. -/
def asTimeExtremumOperand :
    CellObservation → SimpleComparisonOperand TimeOfDay
  | .empty => .notEvaluated
  | .value (.temporal (.time _ parts)) => .value parts true
  | .value _ => .unknown .malformed
  | .unknown cause => .unknown cause
  | .poison cause => .unknown cause

end CellObservation

/-- Evaluate one resolved Time extremum as the shared classified comparison operand. -/
def evalTimeExtremumAggregate (op : TemporalExtremumOp)
    (side : ResolvedTimeAggregateSide) : SimpleComparisonOperand TimeOfDay :=
  evalTemporalExtremumAggregate op.selectTime side

end A12Kernel
