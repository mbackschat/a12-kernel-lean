import A12Kernel.Semantics.DateComparison

/-! # Resolved stored-Date extrema

This capsule implements direct and selected-stream `Min`/`Max` after stored full-Date operands have been classified. Empty operands do not compete, but they retain symmetric missing provenance on any selected result; formal unavailability aborts the complete fold; and an all-empty fold has no synthetic Date value. The result is the existing classified Date comparison operand, so validation polarity uses the one comparison path.

Path/star expansion, actual `Having` evaluation, raw cells, computation targets, constructed-Date calendar identity, DateTime instants, and checked lowering remain outside.
-/

namespace A12Kernel

/-- The two chronological selectors admitted for resolved stored Dates. -/
inductive DateExtremumOp where
  | minimum
  | maximum
  deriving Repr, DecidableEq

namespace DateExtremumOp

/-- Select one resolved full Date, preserving the left value on a chronological tie. -/
def select (op : DateExtremumOp) (left right : FullDate) : FullDate :=
  match op with
  | .minimum => if right.before left then right else left
  | .maximum => if left.before right then right else left

end DateExtremumOp

/-- One already-expanded stored/full-Date aggregate side. `operands` remain in encounter order; the two structural markers add symmetric missing potential without manufacturing a value. -/
structure ResolvedDateAggregateSide where
  operands : List (SimpleComparisonOperand FullDate)
  hasUninstantiatedTail : Bool
  hasHaving : Bool

/-- Scan every classified operand. Empty inputs mark the result missing without entering selection; a reached unavailable input aborts even after a value has been selected. -/
def scanDateExtremumOperands (op : DateExtremumOp) :
    List (SimpleComparisonOperand FullDate) → Option FullDate → Bool →
      Except FormalCause (Option FullDate × Bool)
  | [], selected, allGiven => .ok (selected, allGiven)
  | .unknown cause :: _, _, _ => .error cause
  | .notEvaluated :: operands, selected, _ =>
      scanDateExtremumOperands op operands selected false
  | .value value given :: operands, selected, allGiven =>
      let next :=
        match selected with
        | none => value
        | some current => op.select current value
      scanDateExtremumOperands op operands (some next) (allGiven && given)

/-- Evaluate one resolved stored/full-Date extremum as the existing classified comparison operand. -/
def evalDateExtremumAggregate (op : DateExtremumOp)
    (side : ResolvedDateAggregateSide) : SimpleComparisonOperand FullDate :=
  match scanDateExtremumOperands op side.operands none true with
  | .error cause => .unknown cause
  | .ok (none, _) => .notEvaluated
  | .ok (some selected, allGiven) =>
      .value selected
        (allGiven && !side.hasUninstantiatedTail && !side.hasHaving)

end A12Kernel
