import A12Kernel.Semantics.DateShift

/-! # Admitted full-Date shift laws -/

namespace A12Kernel

/-- Zero day shifting preserves every admitted full Date definitionally. -/
theorem fullDate_addDays_zero (date : FullDate) :
    date.addDays? 0 = some date := by
  cases date with
  | mk civil admissible =>
      simp [FullDate.addDays?, CivilDate.addDays?,
        FullDate.ofCivil?, admissible]

/-- A complete Gregorian era preserves the leap-day label while exercising the bounded coordinate inverse. -/
theorem fullDate_addDays_gregorianEra :
    (FullDate.ofYmd? 2000 2 29).bind (fun date => date.addDays? 146097) =
      FullDate.ofYmd? 2400 2 29 := by
  set_option maxRecDepth 2000 in
    decide

/-- Day shifting also reapplies the universal full-Date floor. -/
theorem fullDate_addDays_belowFloor_none :
    (FullDate.ofYmd? 1583 10 16).bind (fun date => date.addDays? (-1)) = none := by
  set_option maxRecDepth 2000 in
    decide

/-- A real civil landing below the A12 Date floor is retained by expression arithmetic even though the admitted full-Date projection rejects it. -/
theorem civilDate_addDays_retains_belowFullDateFloor :
    (FullDate.ofYmd? 1583 10 16).bind
        (fun date => date.civil.addDays? (-1)) =
        CivilDate.ofYmd? 1583 10 15 ∧
      (FullDate.ofYmd? 1583 10 16).bind
        (fun date => date.addDays? (-1)) = none := by
  set_option maxRecDepth 2000 in
    decide

/-- Month and year shifting are not interchangeable: the year operation preserves a non-leap February end while twelve months do not promote it. -/
theorem fullDate_addMonths_addYears_february_separator :
    (FullDate.ofYmd? 1999 2 28).bind (fun date => date.addMonths? 12) =
        FullDate.ofYmd? 2000 2 28 ∧
      (FullDate.ofYmd? 1999 2 28).bind (fun date => date.addYears? 1) =
        FullDate.ofYmd? 2000 2 29 := by
  decide

/-- Month shifting clamps the source day to the target month's leap-aware final day. -/
theorem fullDate_addMonths_januaryEnd_leapLanding :
    (FullDate.ofYmd? 2020 1 31).bind (fun date => date.addMonths? 1) =
      FullDate.ofYmd? 2020 2 29 := by
  decide

/-- A shift whose result precedes the universal value floor is not admitted as a `FullDate`. -/
theorem fullDate_addMonths_belowFloor_none :
    (FullDate.ofYmd? 1583 10 16).bind (fun date => date.addMonths? (-1)) = none := by
  decide

end A12Kernel
