import A12Kernel.Semantics.DateComparison

/-! # Resolved temporal extrema

This capsule owns the fold shared by direct and selected-stream Date, Time, and DateTime `Min`/`Max` after their operands have been classified. Empty operands do not compete, but they retain symmetric missing provenance on any selected result; formal unavailability aborts the complete fold; and an all-empty fold has no synthetic value. Each temporal family supplies its exact selector and returns its existing classified comparison operand, so validation polarity uses the established comparison path.

Path/star expansion, actual `Having` evaluation, raw cells, computation targets, constructed-Date calendar identity, DateTime parsing and zone resolution, and checked lowering remain outside.
-/

namespace A12Kernel

/-- The two chronological selectors shared by resolved temporal extrema. -/
inductive TemporalExtremumOp where
  | minimum
  | maximum
  deriving Repr, DecidableEq

namespace TemporalExtremumOp

/-- Select one resolved full Date, preserving the left value on a chronological tie. -/
def select (op : TemporalExtremumOp) (left right : FullDate) : FullDate :=
  match op with
  | .minimum => if right.before left then right else left
  | .maximum => if left.before right then right else left

end TemporalExtremumOp

/-- One already-expanded temporal aggregate side. `operands` remain in encounter order; the two structural markers add symmetric missing potential without manufacturing a value. -/
structure ResolvedTemporalAggregateSide (α : Type) where
  operands : List (SimpleComparisonOperand α)
  hasUninstantiatedTail : Bool
  hasHaving : Bool

/-- Scan every classified temporal operand with the caller's exact selector. Empty inputs mark the result missing without entering selection; a reached unavailable input aborts even after a value has been selected. -/
def scanTemporalExtremumOperands (select : α → α → α) :
    List (SimpleComparisonOperand α) → Option α → Bool →
      Except FormalCause (Option α × Bool)
  | [], selected, allGiven => .ok (selected, allGiven)
  | .unknown cause :: _, _, _ => .error cause
  | .notEvaluated :: operands, selected, _ =>
      scanTemporalExtremumOperands select operands selected false
  | .value value given :: operands, selected, allGiven =>
      let next :=
        match selected with
        | none => value
        | some current => select current value
      scanTemporalExtremumOperands select operands (some next) (allGiven && given)

/-- Project a selected temporal extremum into the shared classified comparison operand. -/
def evalTemporalExtremumAggregate (select : α → α → α)
    (side : ResolvedTemporalAggregateSide α) : SimpleComparisonOperand α :=
  match scanTemporalExtremumOperands select side.operands none true with
  | .error cause => .unknown cause
  | .ok (none, _) => .notEvaluated
  | .ok (some selected, allGiven) =>
      .value selected
        (allGiven && !side.hasUninstantiatedTail && !side.hasHaving)

/-- One already-expanded stored/full-Date aggregate side. -/
abbrev ResolvedDateAggregateSide := ResolvedTemporalAggregateSide FullDate

/-- Date-specialized scan retained as the stable API for existing Date laws and consumers. -/
def scanDateExtremumOperands (op : TemporalExtremumOp) :=
  scanTemporalExtremumOperands op.select

/-- Evaluate one resolved stored/full-Date extremum as the existing classified comparison operand. -/
def evalDateExtremumAggregate (op : TemporalExtremumOp)
    (side : ResolvedDateAggregateSide) : SimpleComparisonOperand FullDate :=
  evalTemporalExtremumAggregate op.select side

end A12Kernel
