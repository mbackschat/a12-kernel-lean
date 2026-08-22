import A12Kernel.Semantics.DateRangeOverlap

/-! # Resolved Date-range overlap executable locks

These cases begin with decoded full-Date endpoints and one flat stream of kept, filled range occurrences. They lock the closed-interval relation, its defensive invalid-range guard, and the any-pair scan without adding field reads, authored operand grouping, filtering, polarity, or scalar-versus-list assembly.
-/

namespace A12Kernel.Conformance.DateRangeOverlap

open A12Kernel

private def full (year : Int) (month day : Nat)
    (admissible : (FullDate.ofYmd? year month day).isSome) : FullDate :=
  (FullDate.ofYmd? year month day).get admissible

private def date2024 (month day : Nat)
    (admissible : (FullDate.ofYmd? 2024 month day).isSome) : FullDate :=
  full 2024 month day admissible

private def jan1 := date2024 1 1 (by native_decide)
private def jan15 := date2024 1 15 (by native_decide)
private def jan31 := date2024 1 31 (by native_decide)
private def feb1 := date2024 2 1 (by native_decide)
private def feb28 := date2024 2 28 (by native_decide)
private def mar1 := date2024 3 1 (by native_decide)
private def mar31 := date2024 3 31 (by native_decide)

private def january : ResolvedDateRange :=
  { start := jan1, finish := jan31 }

private def dateValue (date : FullDate) (epochMillis : Int) : DateValue :=
  { instant := { epochMillis }
    parts := date.civil.parts
    basis := .storedGregorian }

private def januaryValue : DateRangeValue :=
  { start := dateValue jan1 1704067200000
    finish := dateValue jan31 1706659200000 }

/- The universal range projects into the established full-Date relation without discarding the richer source value. -/
example : januaryValue.toResolvedDateRange? = some january := by
  native_decide

/- A resolved comparison projection is intentionally narrower than the universal value: equal civil endpoints do not erase exact instant or calendar-basis identity from the source. -/
example :
    let changedIdentity : DateRangeValue := {
      januaryValue with
      start := {
        januaryValue.start with
        instant := { epochMillis := januaryValue.start.instant.epochMillis + 1 }
        basis := .legacyHybrid } }
    januaryValue != changedIdentity ∧
      januaryValue.toResolvedDateRange? = changedIdentity.toResolvedDateRange? := by
  native_decide

/- Either inadmissible endpoint makes the resolved projection unavailable. -/
example :
    (({ januaryValue with
      finish := { januaryValue.finish with
        parts := { year := 2024, month := 2, day := 30 } } } : DateRangeValue)
        |>.toResolvedDateRange?) = none := by
  native_decide

/- Equal ranges overlap. -/
example : january.overlaps january = true := by
  native_decide

/- A shared endpoint belongs to both closed intervals. -/
example :
    january.overlaps { start := jan31, finish := feb28 } = true := by
  native_decide

/- Consecutive dates without a shared endpoint do not overlap. -/
example :
    january.overlaps { start := feb1, finish := feb28 } = false := by
  native_decide

/- Containment overlaps in either argument order. -/
example :
    let inner : ResolvedDateRange := { start := jan15, finish := jan31 }
    january.overlaps inner = true ∧ inner.overlaps january = true := by
  native_decide

/- Strictly separated intervals do not overlap. -/
example :
    january.overlaps { start := feb1, finish := mar1 } = false := by
  native_decide

/- An inverted left interval never overlaps, even when the other interval spans both endpoints. -/
example :
    let inverted : ResolvedDateRange := { start := feb28, finish := feb1 }
    let spanning : ResolvedDateRange := { start := jan1, finish := mar1 }
    inverted.overlaps spanning = false := by
  native_decide

/- The invalid-range guard is symmetric. -/
example :
    let inverted : ResolvedDateRange := { start := feb28, finish := feb1 }
    let spanning : ResolvedDateRange := { start := jan1, finish := mar1 }
    spanning.overlaps inverted = false := by
  native_decide

/- One occurrence does not form a pair. -/
example : anyPairDateRangesOverlap [january] = false := by
  native_decide

/- Two equal occurrences do form a pair; the scan is deliberately not set-like. -/
example : anyPairDateRangesOverlap [january, january] = true := by
  native_decide

/- A disjoint first occurrence does not hide an overlapping pair later in the same list. -/
example :
    let march : ResolvedDateRange := { start := mar1, finish := mar31 }
    let januaryIntoFebruary : ResolvedDateRange :=
      { start := jan15, finish := feb28 }
    anyPairDateRangesOverlap [march, january, januaryIntoFebruary] = true := by
  native_decide

/- A list with no overlapping pair does not fire. -/
example :
    anyPairDateRangesOverlap
      [{ start := jan1, finish := jan15 },
       { start := feb1, finish := feb28 },
       { start := mar1, finish := mar31 }] = false := by
  native_decide

/-! ## Unconfigured yearless intervals

Kernel-measured rows from the [yearless-overlap checkpoint](../../docs/SOURCES.md). Every row
below ran with no Base Year, where the operator compares labels and completes nothing.
-/

/- A month-only pair spans whole months and the interval is closed, so a touching pair overlaps. -/
example :
    let janJun := YearlessInterval.ofMonthPair 1 6
    (janJun.overlaps (YearlessInterval.ofMonthPair 4 9), true) = (true, true) ∧
      (YearlessInterval.ofMonthPair 1 3).overlaps
        (YearlessInterval.ofMonthPair 6 9) = false ∧
      janJun.overlaps (YearlessInterval.ofMonthPair 6 9) = true := by
  native_decide

/- A month-only endpoint reaches inside its month against a day-bearing operand, and stops at the month's edges. -/
example :
    (YearlessInterval.ofMonthPair 1 6).overlaps
        (YearlessInterval.ofMonthDayPair { month := 6, day := 15 }
          { month := 6, day := 20 }) = true ∧
      (YearlessInterval.ofMonthPair 7 12).overlaps
        (YearlessInterval.ofMonthDayPair { month := 6, day := 1 }
          { month := 6, day := 30 }) = false ∧
      (YearlessInterval.ofMonthPair 6 12).overlaps
        (YearlessInterval.ofMonthDayPair { month := 5, day := 1 }
          { month := 6, day := 1 }) = true ∧
      (YearlessInterval.ofMonthPair 1 6).overlaps
        (YearlessInterval.ofMonthDayPair { month := 6, day := 30 }
          { month := 7, day := 31 }) = true := by
  native_decide

/- February reaches day 29 because no year decides leapness, and the span still stops before March. -/
example :
    (YearlessInterval.ofMonthPair 1 2).overlaps
        (YearlessInterval.ofMonthDayPair { month := 2, day := 29 }
          { month := 3, day := 5 }) = true ∧
      (YearlessInterval.ofMonthPair 1 2).overlaps
        (YearlessInterval.ofMonthDayPair { month := 3, day := 1 }
          { month := 3, day := 5 }) = false := by
  native_decide

/- An inverted interval does not overlap anything, matching the resolved guard rather than normalizing the order. -/
example :
    let inverted : YearlessInterval :=
      { start := { month := 9, day := 1 }, finish := { month := 6, day := 1 } }
    inverted.overlaps (YearlessInterval.ofMonthPair 1 12) = false ∧
      (YearlessInterval.ofMonthPair 1 12).overlaps inverted = false ∧
      inverted.direction = .inverted := by
  native_decide

end A12Kernel.Conformance.DateRangeOverlap
