import A12Kernel.Semantics.DateShift

/-! # Admitted full-Date day/month/year shift locks -/

namespace A12Kernel.Conformance.DateShift

open A12Kernel

private def addMonths? (year : Int) (month day : Nat) (offset : Int) :
    Option FullDate :=
  (FullDate.ofYmd? year month day).bind (fun date => date.addMonths? offset)

private def addYears? (year : Int) (month day : Nat) (offset : Int) :
    Option FullDate :=
  (FullDate.ofYmd? year month day).bind (fun date => date.addYears? offset)

private def addDays? (year : Int) (month day : Nat) (offset : Int) :
    Option FullDate :=
  (FullDate.ofYmd? year month day).bind (fun date => date.addDays? offset)

/- Day shifting crosses ordinary, leap, month, and year boundaries in both directions. -/
example :
    addDays? 2020 2 28 1 = FullDate.ofYmd? 2020 2 29 ∧
      addDays? 2020 2 28 2 = FullDate.ofYmd? 2020 3 1 ∧
      addDays? 2021 3 1 (-1) = FullDate.ofYmd? 2021 2 28 ∧
      addDays? 1999 12 31 1 = FullDate.ofYmd? 2000 1 1 := by
  native_decide

/- The bounded coordinate inverse handles a complete Gregorian era independently of the offset's magnitude. -/
example :
    addDays? 2000 2 29 146097 = FullDate.ofYmd? 2400 2 29 := by
  native_decide

/- Calendar-month shifting preserves the day when possible and clamps at the target month's end in both directions. -/
example :
    addMonths? 2020 1 31 1 = FullDate.ofYmd? 2020 2 29 ∧
      addMonths? 2021 1 31 1 = FullDate.ofYmd? 2021 2 28 ∧
      addMonths? 2020 3 31 (-1) = FullDate.ofYmd? 2020 2 29 ∧
      addMonths? 2020 12 15 2 = FullDate.ofYmd? 2021 2 15 := by
  native_decide

/- Calendar-year shifting preserves the last day of February across leap transitions without promoting other February days. -/
example :
    addYears? 1999 2 28 1 = FullDate.ofYmd? 2000 2 29 ∧
      addYears? 2020 2 29 1 = FullDate.ofYmd? 2021 2 28 ∧
      addYears? 2021 2 27 3 = FullDate.ofYmd? 2024 2 27 := by
  native_decide

/- Twelve month shifts and one year shift are observably different at a non-leap February end. -/
example :
    addMonths? 1999 2 28 12 = FullDate.ofYmd? 2000 2 28 ∧
      addYears? 1999 2 28 1 = FullDate.ofYmd? 2000 2 29 := by
  native_decide

/- This boundary returns only admitted full Dates: a result below the universal floor fails closed. -/
example :
    addMonths? 1583 10 16 (-1) = none ∧
      addYears? 1583 10 16 (-1) = none ∧
      addDays? 1583 10 16 (-1) = none := by
  native_decide

end A12Kernel.Conformance.DateShift
