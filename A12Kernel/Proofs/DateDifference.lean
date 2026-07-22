import A12Kernel.Proofs.FullDate
import A12Kernel.Semantics.DateDifference

/-! # Admitted full-Date difference laws -/

namespace A12Kernel

/-- The forward month counter is zero on an equal ordered pair. -/
theorem fullDate_wholeMonthsForward_self (date : FullDate) :
    FullDate.Difference.wholeMonthsForward date date = 0 := by
  simp [FullDate.Difference.wholeMonthsForward,
    DateParts.Difference.wholeMonthsForward,
    DateParts.Difference.monthCoordinate,
    DateParts.Shift.monthLandingDay]
  exact Nat.min_le_left _ _

/-- The forward year counter is zero on an equal ordered pair. -/
theorem fullDate_wholeYearsForward_self (date : FullDate) :
    FullDate.Difference.wholeYearsForward date date = 0 := by
  simp [FullDate.Difference.wholeYearsForward,
    DateParts.Difference.wholeYearsForward,
    DateParts.Shift.yearLandingDay, DateParts.Shift.monthLandingDay]
  split
  · simp_all
  · exact Nat.min_le_left _ _

/-- A Date is zero complete months away from itself. -/
theorem fullDate_differenceInMonths_self (date : FullDate) :
    date.differenceInMonths date = 0 := by
  simp [FullDate.differenceInMonths, FullDate.Difference.signedWholePeriods,
    fullDate_before_irreflexive, fullDate_wholeMonthsForward_self]

/-- A Date is zero complete years away from itself. -/
theorem fullDate_differenceInYears_self (date : FullDate) :
    date.differenceInYears date = 0 := by
  simp [FullDate.differenceInYears, FullDate.Difference.signedWholePeriods,
    fullDate_before_irreflexive, fullDate_wholeYearsForward_self]

/-- Restoring the sign after chronological ordering makes every zero-on-self forward period counter antisymmetric. -/
theorem fullDate_signedWholePeriods_swap
    (forward : FullDate → FullDate → Int)
    (selfZero : ∀ date, forward date date = 0)
    (first second : FullDate) :
    FullDate.Difference.signedWholePeriods forward first second =
      -FullDate.Difference.signedWholePeriods forward second first := by
  by_cases firstBefore : first.before second = true
  · have secondBefore : second.before first = false := by
      cases reverse : second.before first with
      | false => rfl
      | true =>
          exact False.elim
            ((civilDate_before_asymmetric _ _
              ((fullDate_before_iff first second).mp firstBefore))
              ((fullDate_before_iff second first).mp reverse))
    simp [FullDate.Difference.signedWholePeriods, firstBefore, secondBefore]
  · have firstBeforeFalse : first.before second = false := by
      cases forwardResult : first.before second <;> simp_all
    by_cases secondBefore : second.before first = true
    · simp [FullDate.Difference.signedWholePeriods, firstBeforeFalse,
        secondBefore]
    · have secondBeforeFalse : second.before first = false := by
        cases reverseResult : second.before first <;> simp_all
      have notFirstBefore : ¬first.civil.Before second.civil := by
        intro before
        have contradiction := (fullDate_before_iff first second).mpr before
        simp [firstBeforeFalse] at contradiction
      have notSecondBefore : ¬second.civil.Before first.civil := by
        intro before
        have contradiction := (fullDate_before_iff second first).mpr before
        simp [secondBeforeFalse] at contradiction
      have civilEqual : first.civil = second.civil := by
        rcases (civilDate_not_before_iff_eq_or_after
          first.civil second.civil).mp notFirstBefore with equal | after
        · exact equal
        · exact False.elim (notSecondBefore after)
      have equal : first = second := by
        cases first with
        | mk firstCivil firstAdmissible =>
            cases second with
            | mk secondCivil secondAdmissible => simp_all
      subst second
      simp [FullDate.Difference.signedWholePeriods, selfZero]

/-- Signed whole-month difference reverses under operand exchange. -/
theorem fullDate_differenceInMonths_swap (first second : FullDate) :
    first.differenceInMonths second = -second.differenceInMonths first := by
  simpa [FullDate.differenceInMonths] using
    fullDate_signedWholePeriods_swap FullDate.Difference.wholeMonthsForward
      fullDate_wholeMonthsForward_self
      first second

/-- Signed whole-year difference reverses under operand exchange. -/
theorem fullDate_differenceInYears_swap (first second : FullDate) :
    first.differenceInYears second = -second.differenceInYears first := by
  simpa [FullDate.differenceInYears] using
    fullDate_signedWholePeriods_swap FullDate.Difference.wholeYearsForward
      fullDate_wholeYearsForward_self
      first second

/-- The February-end correction makes a nominal year incomplete until the corrected leap-day landing is reached. -/
theorem fullDate_differenceInYears_februaryEnd_boundary :
    (FullDate.ofYmd? 1999 2 28).bind (fun first =>
      (FullDate.ofYmd? 2000 2 28).map first.differenceInYears) = some 0 ∧
    (FullDate.ofYmd? 1999 2 28).bind (fun first =>
      (FullDate.ofYmd? 2000 2 29).map first.differenceInYears) = some 1 := by
  decide

/-- Direct Base Year and its range start denote the same date for both completed-period units. -/
theorem baseYearDateDifference_direct_start_zero (year : Int) :
    baseYearDateDifferenceInMonths year .direct (.range .start) = 0 ∧
      baseYearDateDifferenceInYears year .direct (.range .start) = 0 := by
  have sameNotBefore :
      ¬({ year, month := 1, day := 1 } : DateParts).Before
        { year, month := 1, day := 1 } := by
    simp [DateParts.Before]
  simp [baseYearDateDifferenceInMonths, baseYearDateDifferenceInYears,
    BaseYearDateSource.parts, DateParts.Difference.signedWholePeriods,
    DateParts.Difference.wholeMonthsForward,
    DateParts.Difference.wholeYearsForward,
    DateParts.Difference.monthCoordinate,
    DateParts.Difference.monthLastDay,
    DateParts.daysInMonth?,
    DateParts.Shift.monthLandingDay,
    DateParts.Shift.yearLandingDay, sameNotBefore]

/-- Selecting the opposite end of one configured Base Year yields eleven whole months but no whole year. -/
theorem baseYearDateDifference_finish_boundary (year : Int) :
    baseYearDateDifferenceInMonths year .direct (.range .finish) = 11 ∧
      baseYearDateDifferenceInYears year .direct (.range .finish) = 0 := by
  have before :
      ({ year, month := 1, day := 1 } : DateParts).Before
        { year, month := 12, day := 31 } := by
    simp [DateParts.Before]
  simp [baseYearDateDifferenceInMonths, baseYearDateDifferenceInYears,
    BaseYearDateSource.parts, DateParts.Difference.signedWholePeriods,
    DateParts.Difference.wholeMonthsForward,
    DateParts.Difference.wholeYearsForward,
    DateParts.Difference.monthCoordinate,
    DateParts.Difference.monthLastDay,
    DateParts.daysInMonth?,
    DateParts.Shift.monthLandingDay, before]
  omega

end A12Kernel
