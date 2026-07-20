import A12Kernel.Semantics.DateRangeOverlap

/-! # Resolved Date-range overlap laws

These laws characterize already-decoded endpoint pairs and one flat stream of kept, filled range occurrences. They do not cover cells, authored operand grouping, filtering, polarity, or scalar-versus-list assembly.
-/

namespace A12Kernel

/-- Endpoint order is exactly the result of the existing strict full-Date comparison. -/
theorem dateRange_direction_ordered_iff (range : ResolvedDateRange) :
    range.direction = .ordered ↔
      range.finish.before range.start = false := by
  simp [ResolvedDateRange.direction]

/-- Overlap is exactly two ordered ranges whose closed endpoints are not strictly separated. -/
theorem dateRange_overlaps_iff (left right : ResolvedDateRange) :
    left.overlaps right = true ↔
      left.direction = .ordered ∧
        right.direction = .ordered ∧
        left.finish.before right.start = false ∧
        right.finish.before left.start = false := by
  cases leftDirection : left.direction <;>
    cases rightDirection : right.direction <;>
    simp [ResolvedDateRange.overlaps, leftDirection, rightDirection]

/-- Closed-interval overlap is symmetric. -/
theorem dateRange_overlap_symmetric (left right : ResolvedDateRange) :
    left.overlaps right = right.overlaps left := by
  cases leftDirection : left.direction <;>
    cases rightDirection : right.direction <;>
    simp [ResolvedDateRange.overlaps, leftDirection, rightDirection,
      Bool.and_comm]

/-- A range overlaps itself exactly when its endpoints are ordered. -/
theorem dateRange_overlap_self (range : ResolvedDateRange) :
    range.overlaps range = true ↔ range.direction = .ordered := by
  rw [dateRange_overlaps_iff]
  simp [dateRange_direction_ordered_iff]

/-- An inverted left range never overlaps another range. -/
theorem dateRange_invalid_left_never_overlaps
    (left right : ResolvedDateRange)
    (invalid : left.direction = .inverted) :
    left.overlaps right = false := by
  simp [ResolvedDateRange.overlaps, invalid]

/-- An inverted right range never overlaps another range. -/
theorem dateRange_invalid_right_never_overlaps
    (left right : ResolvedDateRange)
    (invalid : right.direction = .inverted) :
    left.overlaps right = false := by
  simp [ResolvedDateRange.overlaps, invalid]

/-- A strict gap from the left finish to the right start rules overlap out. -/
theorem dateRange_strict_gap_never_overlaps
    (left right : ResolvedDateRange)
    (gap : left.finish.before right.start = true) :
    left.overlaps right = false := by
  cases leftDirection : left.direction <;>
    cases rightDirection : right.direction <;>
    simp [ResolvedDateRange.overlaps, leftDirection, rightDirection, gap]

/-- One occurrence cannot overlap a distinct occurrence because none exists. -/
theorem anyPairDateRangesOverlap_singleton (range : ResolvedDateRange) :
    anyPairDateRangesOverlap [range] = false := by
  rfl

/-- A two-occurrence scan is exactly the primitive overlap relation. -/
theorem anyPairDateRangesOverlap_pair
    (left right : ResolvedDateRange) :
    anyPairDateRangesOverlap [left, right] = left.overlaps right := by
  simp [anyPairDateRangesOverlap]

/-- Two equal occurrences overlap exactly when the shared range is ordered. -/
theorem anyPairDateRangesOverlap_duplicate_iff
    (range : ResolvedDateRange) :
    anyPairDateRangesOverlap [range, range] = true ↔
      range.direction = .ordered := by
  rw [anyPairDateRangesOverlap_pair, dateRange_overlap_self]

end A12Kernel
