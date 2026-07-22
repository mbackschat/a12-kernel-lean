import A12Kernel.Semantics.BaseYearDateSource

/-! # Base-Year Date source executable locks

These cases lock the resolved calendar-part projection of the configured Base Year in date extraction and date-range extraction positions. They deliberately remain before stored/computed Date admission so the unrelated 1583 value floor cannot reject an otherwise configured model year.
-/

namespace A12Kernel.Conformance.BaseYearDateSource

open A12Kernel

/- A direct date source is January 1, and all four direct numeric extractors observe it. -/
example :
    baseYearDateParts 2020 = { year := 2020, month := 1, day := 1 } ∧
      baseYearNumericPart 2020 .day = 1 ∧
      baseYearNumericPart 2020 .month = 1 ∧
      baseYearNumericPart 2020 .quarter = 1 ∧
      baseYearNumericPart 2020 .year = 2020 := by
  native_decide

/- Nested extraction observes the selected range endpoint rather than the direct January 1 meaning. -/
example :
    baseYearRangeNumericPart 2020 .start .day = 1 ∧
      baseYearRangeNumericPart 2020 .finish .day = 31 ∧
      baseYearRangeNumericPart 2020 .finish .month = 12 ∧
      baseYearRangeNumericPart 2020 .finish .quarter = 4 ∧
      baseYearRangeNumericPart 2020 .finish .year = 2020 := by
  native_decide

/- Range extraction chooses the first and final day of the configured year. -/
example :
    baseYearRangeParts 2020 .start =
        { year := 2020, month := 1, day := 1 } ∧
      baseYearRangeParts 2020 .finish =
        { year := 2020, month := 12, day := 31 } := by
  native_decide

/- A pre-floor model year remains a source label; it is not admitted as a stored Date. -/
example :
    baseYearDateParts 1500 = { year := 1500, month := 1, day := 1 } ∧
      baseYearRangeParts 1500 .finish =
        { year := 1500, month := 12, day := 31 } := by
  native_decide

end A12Kernel.Conformance.BaseYearDateSource
