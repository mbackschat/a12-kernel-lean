import A12Kernel.Semantics.ValueList

/-! # Resolved Number aggregates

This capsule starts after one Number field-list or star has been expanded, filtered, and classified. `Sum`, `MinValue`, `MaxValue`, and Number-valued `NumberOfDifferentValues` scan every selected cell, drop empty values from their folds, and retain aggregate-specific missingness for directional validation polarity. `Sum` additionally applies precision-50 arithmetic in encounter order, while distinct count reuses scale-19 Number equality. `SumOfProducts` consumes a separately checked shared-topology stream of row pairs, substitutes empty Number cells with declaration-sensitive zero operands, and stages each multiplication and addition through the same arithmetic core. Path expansion, filtering, and partial relevance remain outside this boundary.
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

/-- One selected Sum cell with the signedness of its own declaration. The cell remains
    in encounter order; signedness matters only when this source is empty. -/
structure ResolvedNumericSumCell where
  cell : ValueListCell .number
  declarationSigned : Bool

/-- A resolved Sum side that retains every selected source's missing direction.
    Uninstantiated declarations contribute no cell but retain their own signedness. -/
structure ResolvedNumericSumSide where
  cells : List ResolvedNumericSumCell
  uninstantiatedSignedness : List Bool
  hasHaving : Bool

namespace ResolvedNumericSumSide

def valueCells (side : ResolvedNumericSumSide) : List (ValueListCell .number) :=
  side.cells.map (·.cell)

def hasEmpty (side : ResolvedNumericSumSide) : Bool :=
  side.cells.any fun source => source.cell.isEmpty

def hasMissingPotential (side : ResolvedNumericSumSide) : Bool :=
  side.hasEmpty || !side.uninstantiatedSignedness.isEmpty

/-- Whether any missing source can contribute a negative value after filling. -/
def hasSignedMissing (side : ResolvedNumericSumSide) : Bool :=
  side.cells.any (fun source => source.cell.isEmpty && source.declarationSigned) ||
    side.uninstantiatedSignedness.any id

end ResolvedNumericSumSide

/-- Evaluate resolved Number `Sum` while retaining signedness per selected or
    uninstantiated declaration. Present declarations do not affect missing directions. -/
def evalDeclaredNumericSumAggregate (side : ResolvedNumericSumSide) : NumericOperand :=
  match scanNumericSumCells side.valueCells with
  | .error cause => .unknown cause
  | .ok total =>
      let amount := total.getD 0
      let fillability :=
        if side.hasHaving then
          NumericFillability.both
        else if side.hasMissingPotential then
          match total with
          | none => NumericFillability.both
          | some _ => NumericFillability.emptyNumber side.hasSignedMissing
        else
          NumericFillability.fixed
      .value amount fillability

/-- Embed the former one-signedness profile into the per-declaration representation. -/
def ResolvedValueListSide.toNumericSumSide (side : ResolvedValueListSide .number)
    (fieldSigned : Bool) : ResolvedNumericSumSide :=
  { cells := side.cells.map fun cell => { cell, declarationSigned := fieldSigned }
    uninstantiatedSignedness := if side.hasUninstantiatedTail then [fieldSigned] else []
    hasHaving := side.hasHaving }

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

/-- Compatibility projection for one declaration-signedness profile. -/
def evalNumericSumAggregate (fieldSigned : Bool)
    (side : ResolvedValueListSide .number) : NumericOperand :=
  evalDeclaredNumericSumAggregate (side.toNumericSumSide fieldSigned)

/-- Insert a Number into the already-seen representatives exactly when no scale-19-equal representative exists. Representative order is internal and does not affect the count. -/
def insertDistinctNumericValue (seen : List Rat) (value : Rat) : List Rat :=
  if seen.any fun candidate =>
      ValueListAtom.equal (kind := .number) candidate value then
    seen
  else
    value :: seen

/-- Scan one resolved Number aggregate side, skipping empty cells and stopping at the first formal unavailability. -/
def scanDistinctNumericCells (cells : List (ValueListCell .number)) :
    Except FormalCause (List Rat) :=
  ValueListCell.scanPresent (kind := .number)
    insertDistinctNumericValue cells []

/-- Evaluate Number-valued `NumberOfDifferentValues`. Only distinct filled values count. Missing cells or a declared tail can only increase the current count; a reached filter can also remove currently selected values and is therefore both-directionally fillable. -/
def evalNumericDistinctCountAggregate
    (side : ResolvedValueListSide .number) : NumericOperand :=
  match scanDistinctNumericCells side.cells with
  | .error cause => .unknown cause
  | .ok seen =>
      let fillability :=
        if side.hasHaving then
          NumericFillability.both
        else if side.hasMissingPotential then
          NumericFillability.growOnly
        else
          NumericFillability.fixed
      .value seen.length fillability

/-- One row-aligned pair consumed by `SumOfProducts`. Empty cells remain explicit so each declaration can supply its own numeric missing direction before multiplication. -/
structure ResolvedNumericProductRow where
  left : ValueListCell .number
  right : ValueListCell .number

/-- The resolved `SumOfProducts` input. Its rows already share one canonical topology; the tail records an omitted row at any reopened level. -/
structure ResolvedNumericProductSide where
  rows : List ResolvedNumericProductRow
  leftSigned : Bool
  rightSigned : Bool
  hasUninstantiatedTail : Bool

def numericProductCell
    (signed : Bool) : ValueListCell .number →
      Except FormalCause (Rat × NumericFillability)
  | .present amount => pure (amount, .fixed)
  | .empty => pure (0, .emptyNumber signed)
  | .unknown cause => throw cause

def numericProductStep
    (total left right : Rat × NumericFillability) :
      Rat × NumericFillability :=
  let productAmount := NumericArithmeticOp.multiply.eval left.1 right.1
  let productFill := NumericArithmeticOp.multiply.fillability
    left.1 left.2 right.1 right.2
  (NumericArithmeticOp.add.eval total.1 productAmount,
    NumericArithmeticOp.add.fillability total.1 total.2
      productAmount productFill)

def scanNumericProductRowsFrom (side : ResolvedNumericProductSide) :
    List ResolvedNumericProductRow → Rat × NumericFillability →
      Except FormalCause (Rat × NumericFillability)
  | [], total => pure total
  | row :: remaining, total => do
      let left ← numericProductCell side.leftSigned row.left
      let right ← numericProductCell side.rightSigned row.right
      scanNumericProductRowsFrom side remaining
        (numericProductStep total left right)

/-- Scan row pairs in canonical order. Each multiplication and following addition crosses the existing precision-50 boundary; the left cell is reached before the right cell. -/
def scanNumericProductRows (side : ResolvedNumericProductSide) :
    Except FormalCause (Rat × NumericFillability) :=
  scanNumericProductRowsFrom side side.rows (0, .fixed)

/-- Evaluate row-aligned `SumOfProducts`. Empty cells substitute numeric zero with declaration-owned fillability, a first unavailable reached cell suppresses the result, and any omitted declared row makes a successful result movable in both directions. -/
def evalNumericProductAggregate
    (side : ResolvedNumericProductSide) : NumericOperand :=
  match scanNumericProductRows side with
  | .error cause => .unknown cause
  | .ok (amount, fillability) =>
      .value amount (if side.hasUninstantiatedTail then .both else fillability)

end A12Kernel
