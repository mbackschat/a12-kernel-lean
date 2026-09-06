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

namespace CellObservation

/-- Classify one phase-observed cell as a complete-Date extremum operand.

    This is the missing step between a checked cell and the fold: the fold has always been parametric in its element type, and nothing projected a document's cells into the Date one. It follows `asDirectNumericComparisonOperand`'s shape, with the Date family's own empty rule — an unspecified operand does **not** compete and does not contribute a synthetic value, where an empty Number would contribute zero.

    A payload that is not a Date, and a Date whose stored parts name no representable calendar date, both fail closed as malformed rather than being skipped. Skipping them would let a broken cell read as an absent one, and the fold's own missing-provenance flag would then report a complete stream. -/
def asDateExtremumOperand :
    CellObservation → SimpleComparisonOperand FullDate
  | .empty => .notEvaluated
  | .value (.temporal (.date dateValue)) =>
      match dateValue.toFullDate? with
      | some date => .value date true
      | none => .unknown .malformed
  | .value _ => .unknown .malformed
  | .unknown cause => .unknown cause
  | .poison cause => .unknown cause

end CellObservation

/-! ## The reduced-precision arms

A component-omitting Date list is admitted and **ordered** by the Kernel at the shared set's own
precision, the yearless case even with no Base Year declared
([checkpoint](../../docs/sources/evaluation-and-application-routes.md#src-extrema-component-omitting-fold)).
No interval domain is involved: within one shared component set the canonical representative is
order-preserving, so a year-bearing set orders as `FullDate` and a yearless one as `MonthDayValue`,
each through the generic scan above. The omitted components are supplied by `maskedDateComponents`
rather than read off the cell, for the reason that projection states.
-/

/-- Select one yearless calendar position, preserving the left value on a tie — the same left-biased
    rule the full-Date selector applies, over the ordering `MonthDayValue` already carries. -/
def TemporalExtremumOp.selectMonthDay (op : TemporalExtremumOp)
    (left right : MonthDayValue) : MonthDayValue :=
  match op with
  | .minimum => if right.before left then right else left
  | .maximum => if left.before right then right else left

/-- One already-expanded yearless-Date aggregate side. -/
abbrev ResolvedYearlessDateAggregateSide := ResolvedTemporalAggregateSide MonthDayValue

namespace CellObservation

/-- Classify one phase-observed cell as a **year-bearing component-omitting** Date extremum operand:
    the decoded parts reduced to the declared set, with the model's Base Year supplying a yearless
    declaration's year. A set naming every date component reduces to the ordinary projection, so this
    is a widening of `asDateExtremumOperand` and not a rival to it. -/
def asMaskedDateExtremumOperand (components : TemporalComponents) (baseYear : Option Int) :
    CellObservation → SimpleComparisonOperand FullDate
  | .empty => .notEvaluated
  | .value (.temporal (.date dateValue)) =>
      let (year, month, day) := maskedDateComponents components baseYear dateValue.parts
      match FullDate.ofYmd? year month day with
      | some date => .value date true
      | none => .unknown .malformed
  | .value _ => .unknown .malformed
  | .unknown cause => .unknown cause
  | .poison cause => .unknown cause

/-- Classify one phase-observed cell as a **yearless** Date extremum operand: the calendar position
    the declaration spells, with a set that omits the day taking its canonical first. No year is
    available to complete either side, so the yearless position *is* the ordered value rather than a
    projection of one — completing it against an invented year would order two such values by that
    invention. -/
def asYearlessDateExtremumOperand (components : TemporalComponents) :
    CellObservation → SimpleComparisonOperand MonthDayValue
  | .empty => .notEvaluated
  | .value (.temporal (.date dateValue)) =>
      let (_, month, day) := maskedDateComponents components none dateValue.parts
      .value { month, day } true
  | .value _ => .unknown .malformed
  | .unknown cause => .unknown cause
  | .poison cause => .unknown cause

end CellObservation

/-- Evaluate one resolved yearless-Date extremum through the shared scan. -/
def evalYearlessDateExtremumAggregate (op : TemporalExtremumOp)
    (side : ResolvedYearlessDateAggregateSide) : SimpleComparisonOperand MonthDayValue :=
  evalTemporalExtremumAggregate op.selectMonthDay side

/-- Date-specialized scan retained as the stable API for existing Date laws and consumers. -/
def scanDateExtremumOperands (op : TemporalExtremumOp) :=
  scanTemporalExtremumOperands op.select

/-- Evaluate one resolved stored/full-Date extremum as the existing classified comparison operand. -/
def evalDateExtremumAggregate (op : TemporalExtremumOp)
    (side : ResolvedDateAggregateSide) : SimpleComparisonOperand FullDate :=
  evalTemporalExtremumAggregate op.select side

end A12Kernel
