import A12Kernel.Semantics.ValueList

/-! # Resolved Number aggregate extrema

This capsule starts after one Number field-list or star has been expanded, filtered, and classified. `MinValue` and `MaxValue` scan every selected cell, drop empty values from selection, and retain aggregate-specific missingness only for directional validation polarity. Path expansion, filter evaluation, partial relevance, and computation are outside this boundary.
-/

namespace A12Kernel

namespace NumericExtremumOp

/-- Scan an already-selected Number stream in order. Empty cells do not compete; the first unavailable selected cell stops the scan; present values use the shared exact selector without a synthetic zero seed. -/
def scanAggregateCells (op : NumericExtremumOp) :
    List (ValueListCell .number) → Option Rat → Except FormalCause (Option Rat)
  | [], selected => .ok selected
  | .empty :: cells, selected => op.scanAggregateCells cells selected
  | .unknown cause :: _, _ => .error cause
  | .present amount :: cells, none => op.scanAggregateCells cells (some amount)
  | .present amount :: cells, some selected =>
      op.scanAggregateCells cells (some (op.selectAmount selected amount))

/-- Once at least one value has entered an incomplete aggregate fold, a future value may only raise `MaxValue` or lower `MinValue`. The all-empty zero identity is handled separately. -/
def presentAggregateFillability : NumericExtremumOp → NumericFillability
  | .minimum => .shrinkOnly
  | .maximum => .growOnly

end NumericExtremumOp

/-- Evaluate resolved Number `MinValue`/`MaxValue` as a validation operand. A resolved `Having` marker makes every available result both-directionally fillable. Without one, an incomplete fold with a present value uses the selector direction, while an all-empty authored selection yields the kernel's conservative both-directionally fillable zero. The no-cell/no-marker totality state is fixed zero and is not claimed authored-reachable. -/
def evalNumericExtremumAggregate (op : NumericExtremumOp)
    (side : ResolvedValueListSide .number) : NumericOperand :=
  match op.scanAggregateCells side.cells none with
  | .error cause => .unknown cause
  | .ok selected =>
      let amount := selected.getD 0
      let fillability :=
        if side.hasHaving then
          NumericFillability.both
        else if side.hasMissingPotential then
          match selected with
          | none => NumericFillability.both
          | some _ => op.presentAggregateFillability
        else
          NumericFillability.fixed
      .value amount fillability

end A12Kernel
