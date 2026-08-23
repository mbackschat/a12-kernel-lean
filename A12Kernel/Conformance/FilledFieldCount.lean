import A12Kernel.Semantics.FieldFillQuantifier

/-! # `NumberOfFilledFields` locks

The count family's field member. Every row below is read off the kernel's own `validateFull` at 30.8.1
on **both** codegen strategies, which agreed on all four observations.

The measurement compared the count against `0`, `1`, and `2` with three rules over one two-operand
count, so each row's firing names the count itself rather than a direction. -/

namespace A12Kernel.Conformance.FilledFieldCount

open A12Kernel

private def filled : CellObservation := .value (.str "x")

private def invalid : CellObservation := .unknown .dateFormat

/- **The load-bearing row.** One filled operand beside one formally invalid operand makes the whole
count **unavailable**: the Kernel reported the invalid operand's own formal error and fired none of the
three comparisons. So an invalid operand is neither skipped, which would have counted `1`, nor treated as
filled, which would have counted `2`. -/
example :
    numberOfFilledFields [filled, invalid] = .unknown ∧
      numberOfFilledFields [invalid, filled] = .unknown ∧
      numberOfFilledFields [invalid] = .unknown := by
  native_decide

/- **An empty cell is never counted, and emptiness is not unavailability.** A filled operand beside an
empty one counts one, and an all-empty list counts zero and compares normally rather than answering
unknown — which is the row that separates "empty" from "invalid" in this operator. -/
example :
    numberOfFilledFields [filled, .empty] = .value 1 ∧
      numberOfFilledFields [.empty, .empty] = .value 0 ∧
      numberOfFilledFields [] = .value 0 := by
  native_decide

/- Two filled operands count two, so the counting itself is exercised rather than only its edges. -/
example :
    numberOfFilledFields [filled, filled] = .value 2 ∧
      numberOfFilledFields [filled, filled, .empty, filled] = .value 3 := by
  native_decide

/- One invalid operand poisons the count regardless of how many filled ones accompany it, so the
unavailability is not a tie-break that a majority of filled operands could win. -/
example :
    numberOfFilledFields [filled, filled, invalid, filled] = .unknown := by
  native_decide

/- A `poison` observation is the computation face of the same invalidity and cannot reach this
validation arm. It is folded into unknown rather than counted, so a misrouted observation fails closed.
**Internal, not measured:** the computation arm itself is deliberately absent, because the group count's
two arms differ exactly here and no observation authorises assuming this one follows either. -/
example :
    numberOfFilledFields [filled, .poison .dateFormat] = .unknown := by
  native_decide

end A12Kernel.Conformance.FilledFieldCount
