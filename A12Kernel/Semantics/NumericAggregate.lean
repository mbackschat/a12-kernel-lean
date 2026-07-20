import A12Kernel.Semantics.ValueList

/-! # Resolved Number aggregates

This capsule starts after one Number field-list or star has been expanded, filtered, and classified. `Sum`, `MinValue`, and `MaxValue` scan every selected cell, drop empty values from their numeric folds, and retain aggregate-specific missingness for directional validation polarity. `Sum` additionally applies precision-50 arithmetic in encounter order. Path expansion, filter evaluation, partial relevance, and computation are outside this boundary.
-/

namespace A12Kernel

namespace NumericExtremumOp

/-- Add one present value to the optional aggregate-extremum accumulator. -/
def aggregateStep (op : NumericExtremumOp) : Option Rat → Rat → Option Rat
  | none, amount => some amount
  | some selected, amount => some (op.selectAmount selected amount)

/-- Scan an already-selected Number stream in order. Empty cells do not compete; the first unavailable selected cell stops the scan; present values use the shared exact selector without a synthetic zero seed. -/
def scanAggregateCells (op : NumericExtremumOp) :
    List (ValueListCell .number) → Option Rat → Except FormalCause (Option Rat)
  | cells, selected =>
      ValueListCell.scanPresent (kind := .number) op.aggregateStep cells selected

/-- Once at least one value has entered an incomplete aggregate fold, a future value may only raise `MaxValue` or lower `MinValue`. The all-empty zero identity is handled separately. -/
def presentAggregateFillability : NumericExtremumOp → NumericFillability
  | .minimum => .shrinkOnly
  | .maximum => .growOnly

end NumericExtremumOp

/-- Add one present value to an encounter-ordered Number sum. `none` means no value has entered yet, not that the current total is zero; the first present value is still added to zero through the precision-50 arithmetic boundary. -/
def numericSumStep : Option Rat → Rat → Option Rat
  | none, amount => some (NumericArithmeticOp.add.eval 0 amount)
  | some total, amount => some (NumericArithmeticOp.add.eval total amount)

/-- Scan one resolved Number aggregate side as a precision-50 encounter-ordered sum. -/
def scanNumericSumCells (cells : List (ValueListCell .number)) :
    Except FormalCause (Option Rat) :=
  ValueListCell.scanPresent (kind := .number) numericSumStep cells none

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

/-- Evaluate resolved Number `Sum` as a validation operand for one declaration-signedness profile. A resolved `Having` marker makes every available result both-directionally fillable. Otherwise an incomplete sum with at least one present value grows and may shrink only when its omitted declaration is signed; an all-empty authored selection yields the conservative both-directionally fillable zero. Mixed-declaration missingness remains outside this boundary because it requires signedness per missing source, not one global flag. -/
def evalNumericSumAggregate (fieldSigned : Bool)
    (side : ResolvedValueListSide .number) : NumericOperand :=
  match scanNumericSumCells side.cells with
  | .error cause => .unknown cause
  | .ok total =>
      let amount := total.getD 0
      let fillability :=
        if side.hasHaving then
          NumericFillability.both
        else if side.hasMissingPotential then
          match total with
          | none => NumericFillability.both
          | some _ => NumericFillability.emptyNumber fieldSigned
        else
          NumericFillability.fixed
      .value amount fillability

end A12Kernel
