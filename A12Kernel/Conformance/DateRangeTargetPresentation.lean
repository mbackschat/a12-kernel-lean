import A12Kernel.Elaboration.DateRangeTargetPresentation

/-! # Stored DateRange target-text locks

These cases pin the exact stored text of each yearless presentation. No current target
route reaches the two lexical variants; the text is locked here because the Kernel rows
that measured it are retained, so opening a route later cannot silently change it.
-/

namespace A12Kernel.Conformance.DateRangeTargetPresentation

open A12Kernel

/- The empty separator concatenates its two months, and the dotted presentation spells day before month on both endpoints. Both differ from the slash-separated presentation that retains the same components. -/
example :
    (DateRangeInputFormat.renderYearlessMonthConcatenated 6 9).text = "0609" ∧
      (DateRangeInputFormat.renderYearlessDayMonthDotted
        { month := 6, day := 1 } { month := 9, day := 30 }).text = "01.06-30.09" ∧
      (DateRangeInputFormat.renderYearlessMonth 6 9).text = "06/09" ∧
      (DateRangeInputFormat.renderYearlessMonthDay
        { month := 6, day := 1 } { month := 9, day := 30 }).text = "06-01/09-30" := by
  native_decide

/- A single-digit month keeps its leading zero on both sides of a concatenated pair, which is the only place where dropping the pad would still parse. -/
example :
    (DateRangeInputFormat.renderYearlessMonthConcatenated 1 12).text = "0112" := by
  native_decide

end A12Kernel.Conformance.DateRangeTargetPresentation
