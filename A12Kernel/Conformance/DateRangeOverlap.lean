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

end A12Kernel.Conformance.DateRangeOverlap
