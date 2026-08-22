import A12Kernel.Semantics.FullDate

/-! # Resolved Date-range overlap

This capsule starts after both endpoints have been decoded and admitted as full Date values. It deliberately keeps inverted ranges representable because the overlap predicate treats them as non-overlapping rather than assuming ordered input. Field observation, skipped-cell derivation, authored operand grouping, filtering, polarity, and scalar-versus-list assembly belong to later consuming capsules.
-/

namespace A12Kernel

/-- Two resolved full-Date endpoints before the overlap predicate applies its ordering guard. -/
structure ResolvedDateRange where
  start : FullDate
  finish : FullDate
  deriving Repr, DecidableEq

namespace DateValue

/-- Project one universal Date endpoint into the established real, floor-admitted full-Date domain. Exact instant and calendar provenance remain available on the source value. -/
def toFullDate? (value : DateValue) : Option FullDate :=
  FullDate.ofYmd? value.parts.year value.parts.month value.parts.day

end DateValue

namespace DateRangeValue

/-- Project both endpoints into the established resolved range exactly when both are admitted full Dates. -/
def toResolvedDateRange? (value : DateRangeValue) : Option ResolvedDateRange := do
  let start ← value.start.toFullDate?
  let finish ← value.finish.toFullDate?
  pure { start, finish }

end DateRangeValue

/-- The resolved endpoint order kept explicit so inversion cannot be silently normalized. -/
inductive DateRangeDirection where
  | ordered
  | inverted
  deriving Repr, DecidableEq

namespace ResolvedDateRange

/-- Classify the supplied endpoint order. Equal endpoints form an ordered one-day range. -/
def direction (range : ResolvedDateRange) : DateRangeDirection :=
  if range.finish.before range.start then .inverted else .ordered

/-- Closed-interval overlap with the kernel's explicit invalid-range guard. -/
def overlaps (left right : ResolvedDateRange) : Bool :=
  match left.direction, right.direction with
  | .ordered, .ordered =>
      !left.finish.before right.start &&
        !right.finish.before left.start
  | _, _ => false

end ResolvedDateRange

/-! ## Unconfigured yearless intervals

A model with no Base Year has no year to complete a yearless declaration with, and the
Kernel compares such ranges as month/day labels rather than refusing them. The interval a
declaration denotes therefore depends on its declared components: a month-only pair spans
whole months, while a day-bearing pair keeps its authored days.
-/

/-- One closed interval of yearless month/day labels. -/
structure YearlessInterval where
  start : MonthDayValue
  finish : MonthDayValue
  deriving Repr, DecidableEq

namespace YearlessInterval

/-- The greatest day any year admits for one month. February reaches 29 because no year is
available to decide leapness, which is what the Kernel compares against; a month outside
1–12 has no admitted day. -/
def yearlessLastDay : Nat → Nat
  | 1 => 31
  | 2 => 29
  | 3 => 31
  | 4 => 30
  | 5 => 31
  | 6 => 30
  | 7 => 31
  | 8 => 31
  | 9 => 30
  | 10 => 31
  | 11 => 30
  | 12 => 31
  | _ => 0

/-- The interval a month-only declaration denotes: the first day of its start month through
the last day its finish month can ever have. -/
def ofMonthPair (start finish : Nat) : YearlessInterval := {
  start := { month := start, day := 1 }
  finish := { month := finish, day := yearlessLastDay finish }
}

/-- The interval a day-bearing yearless declaration denotes, retaining both authored days. -/
def ofMonthDayPair (start finish : MonthDayValue) : YearlessInterval :=
  { start, finish }

/-- Classify the authored label order. Equal labels form an ordered one-day interval. -/
def direction (interval : YearlessInterval) : DateRangeDirection :=
  if interval.finish.before interval.start then .inverted else .ordered

/-- Closed-interval overlap on labels, keeping the same invalid-range guard the resolved
relation uses so an inverted interval is never silently normalized. -/
def overlaps (left right : YearlessInterval) : Bool :=
  match left.direction, right.direction with
  | .ordered, .ordered =>
      !left.finish.before right.start && !right.finish.before left.start
  | _, _ => false

end YearlessInterval

/-- Whether any two distinct occurrences in one ordered resolved stream overlap. Equal range values at two positions remain two occurrences. -/
def anyPairDateRangesOverlap : List ResolvedDateRange → Bool
  | [] => false
  | current :: rest =>
      rest.any current.overlaps || anyPairDateRangesOverlap rest

end A12Kernel
