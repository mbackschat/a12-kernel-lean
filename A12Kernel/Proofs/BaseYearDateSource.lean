import A12Kernel.Semantics.BaseYearDateSource

/-! # Base-Year Date source laws

These laws characterize the resolved calendar labels used by direct date extraction and date-range extraction. They do not prove authored checking, model-zone instant resolution, stored-value legality, or a complete range consumer.
-/

namespace A12Kernel

/-- The direct Base-Year date source exposes January 1 and the expected four numeric components. -/
theorem baseYearDateSource_components (year : Int) :
    baseYearDateParts year = { year, month := 1, day := 1 } ∧
      baseYearNumericPart year .day = 1 ∧
      baseYearNumericPart year .month = 1 ∧
      baseYearNumericPart year .quarter = 1 ∧
      baseYearNumericPart year .year = year := by
  simp [baseYearDateParts, baseYearNumericPart,
    BaseYearDateSource.parts, baseYearDateSourceNumericPart,
    DateNumericPart.extract]

/-- Range extraction exposes the exact first and final calendar labels of the configured year. -/
theorem baseYearRangeParts_endpoints (year : Int) :
    baseYearRangeParts year .start = { year, month := 1, day := 1 } ∧
      baseYearRangeParts year .finish = { year, month := 12, day := 31 } := by
  simp [baseYearRangeParts, BaseYearDateSource.parts]

/-- Start and finish remain distinct; a consumer must not collapse both range positions to the direct January 1 source. -/
theorem baseYearRangeParts_start_ne_finish (year : Int) :
    baseYearRangeParts year .start ≠ baseYearRangeParts year .finish := by
  simp [baseYearRangeParts, BaseYearDateSource.parts]

/-- Selecting the range start before numeric extraction is extensionally the direct January 1 Base-Year source for every component. -/
theorem baseYearRangeNumericPart_start_eq_direct
    (year : Int) (part : DateNumericPart) :
    baseYearRangeNumericPart year .start part =
      baseYearNumericPart year part := by
  rfl

/-- The selected finish label exposes the final day, month, quarter, and configured year. -/
theorem baseYearRangeFinish_numericParts (year : Int) :
    baseYearRangeNumericPart year .finish .day = 31 ∧
      baseYearRangeNumericPart year .finish .month = 12 ∧
      baseYearRangeNumericPart year .finish .quarter = 4 ∧
      baseYearRangeNumericPart year .finish .year = year := by
  simp [baseYearRangeNumericPart, baseYearDateSourceNumericPart,
    BaseYearDateSource.parts, DateNumericPart.extract]

end A12Kernel
