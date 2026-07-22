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
  simp [baseYearDateParts, baseYearNumericPart, DateNumericPart.extract]

/-- Range extraction exposes the exact first and final calendar labels of the configured year. -/
theorem baseYearRangeParts_endpoints (year : Int) :
    baseYearRangeParts year .start = { year, month := 1, day := 1 } ∧
      baseYearRangeParts year .finish = { year, month := 12, day := 31 } := by
  simp [baseYearRangeParts, baseYearDateParts]

/-- Start and finish remain distinct; a consumer must not collapse both range positions to the direct January 1 source. -/
theorem baseYearRangeParts_start_ne_finish (year : Int) :
    baseYearRangeParts year .start ≠ baseYearRangeParts year .finish := by
  simp [baseYearRangeParts, baseYearDateParts]

end A12Kernel
