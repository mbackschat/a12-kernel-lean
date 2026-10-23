import A12Kernel.Proofs.DateShift
import A12Kernel.Semantics.BerlinLegacyCalendarArithmetic

/-! # Berlin legacy calendar arithmetic laws

These laws characterize the field mutations and shared signed completed-period API over the pinned versioned Berlin profile. They do not claim correspondence for another zone or calendar basis.
-/

namespace A12Kernel

/-- A zero-day Berlin landing preserves both the decoded local state and its already
    selected exact instant; it never re-resolves an ambiguous wall label. -/
@[simp] theorem berlin_calendarDayLanding_zero
    (dateTime : LegacyCalendarLabel) (instant : Instant) :
    EuropeBerlinLegacyProfile.calendarDayLanding?
        dateTime instant 0 =
      some (dateTime, instant) := by
  simp [EuropeBerlinLegacyProfile.calendarDayLanding?]

/-- A zero-month Berlin mutation preserves the already selected exact instant; even an ambiguous source label is not resolved again. -/
@[simp] theorem berlin_calendarMonthLanding_zero
    (dateTime : LegacyCalendarLabel) (instant : Instant) :
    EuropeBerlinLegacyProfile.calendarMonthLanding?
        dateTime instant 0 =
      some (dateTime, instant) := by
  simp [EuropeBerlinLegacyProfile.calendarMonthLanding?]

/-- A zero-year Berlin mutation preserves the already selected exact instant; even an ambiguous source label is not resolved again. -/
@[simp] theorem berlin_calendarYearLanding_zero
    (dateTime : LegacyCalendarLabel) (instant : Instant) :
    EuropeBerlinLegacyProfile.calendarYearLanding?
        dateTime instant 0 =
      some (dateTime, instant) := by
  simp [EuropeBerlinLegacyProfile.calendarYearLanding?]

/-- Every successful nonzero Berlin day mutation lands on its nominal hybrid-calendar target date even when an offset re-fit changes the clock or exact instant. A zero mutation returns its source unchanged, whether or not that label is real. -/
theorem berlin_calendarDayLanding_preserves_date
    (current landed : LegacyCalendarLabel) (currentInstant landedInstant : Instant)
    (days : Int) (nonzero : days ≠ 0)
    (result :
      EuropeBerlinLegacyProfile.calendarDayLanding?
          current currentInstant days =
        some (landed, landedInstant)) :
    DateParts.LegacyHybrid.addDays? current.parts days = some landed.parts := by
  simp only [EuropeBerlinLegacyProfile.calendarDayLanding?, nonzero,
    ↓reduceIte] at result
  cases nextDateEq : DateParts.LegacyHybrid.addDays? current.parts days with
  | none => simp [nextDateEq] at result
  | some nextDate =>
      cases landingEq :
          EuropeBerlinLegacyProfile.calendarDayTargetLanding?
            current currentInstant nextDate with
      | none => simp [nextDateEq, landingEq] at result
      | some landing =>
          simp [nextDateEq, landingEq] at result
          have dateEq : nextDate = landed.parts :=
            congrArg LegacyCalendarLabel.parts result.1
          simp [dateEq]

/-- A zero year candidate cannot underflow the completed-period count. -/
@[simp] theorem berlin_wholeYearsForward_same_label
    (dateTime : LegacyCalendarLabel) (firstInstant secondInstant : Instant) :
    EuropeBerlinLegacyProfile.wholeYearsForward?
        dateTime firstInstant dateTime secondInstant =
      some 0 := by
  simp [EuropeBerlinLegacyProfile.wholeYearsForward?,
    berlin_calendarYearLanding_zero]

/-- Exact-instant ordering makes every completed-period wrapper zero on identical operands, independently of its forward calculator. -/
@[simp] theorem berlin_signedWholePeriods_self
    (forward :
      LegacyCalendarLabel → Instant → LegacyCalendarLabel → Instant → Option Nat)
    (dateTime : LegacyCalendarLabel) (instant : Instant) :
    EuropeBerlinLegacyProfile.signedWholePeriods?
        forward dateTime instant dateTime instant =
      some 0 := by
  simp [EuropeBerlinLegacyProfile.signedWholePeriods?]

/-- The shared exact-instant sign wrapper is antisymmetric for every forward completed-period calculator. -/
theorem berlin_signedWholePeriods_swap
    (forward :
      LegacyCalendarLabel → Instant → LegacyCalendarLabel → Instant → Option Nat)
    (first : LegacyCalendarLabel) (firstInstant : Instant)
    (second : LegacyCalendarLabel) (secondInstant : Instant) :
    (EuropeBerlinLegacyProfile.signedWholePeriods?
      forward first firstInstant second secondInstant).map (-·) =
    EuropeBerlinLegacyProfile.signedWholePeriods?
      forward second secondInstant first firstInstant := by
  by_cases before : firstInstant.epochMillis < secondInstant.epochMillis
  · have notAfter : ¬secondInstant.epochMillis < firstInstant.epochMillis := by
      omega
    simp [EuropeBerlinLegacyProfile.signedWholePeriods?,
      before, notAfter, Function.comp_def]
  · by_cases after : secondInstant.epochMillis < firstInstant.epochMillis
    · simp [EuropeBerlinLegacyProfile.signedWholePeriods?,
        before, after, Function.comp_def]
    · simp [EuropeBerlinLegacyProfile.signedWholePeriods?,
        before, after]

/- Month and year laws are direct specializations of the shared completed-period sign wrapper. -/
@[simp] theorem berlin_differenceResolvedInMonths_self
    (dateTime : LegacyCalendarLabel) (instant : Instant) :
    EuropeBerlinLegacyProfile.differenceResolvedInMonths?
        dateTime instant dateTime instant =
      some 0 := by
  exact berlin_signedWholePeriods_self
    EuropeBerlinLegacyProfile.wholeMonthsForward? dateTime instant

theorem berlin_differenceResolvedInMonths_swap
    (first : LegacyCalendarLabel) (firstInstant : Instant)
    (second : LegacyCalendarLabel) (secondInstant : Instant) :
    (EuropeBerlinLegacyProfile.differenceResolvedInMonths?
      first firstInstant second secondInstant).map (-·) =
    EuropeBerlinLegacyProfile.differenceResolvedInMonths?
      second secondInstant first firstInstant := by
  exact berlin_signedWholePeriods_swap
    EuropeBerlinLegacyProfile.wholeMonthsForward?
    first firstInstant second secondInstant

@[simp] theorem berlin_differenceResolvedInYears_self
    (dateTime : LegacyCalendarLabel) (instant : Instant) :
    EuropeBerlinLegacyProfile.differenceResolvedInYears?
        dateTime instant dateTime instant =
      some 0 := by
  exact berlin_signedWholePeriods_self
    EuropeBerlinLegacyProfile.wholeYearsForward? dateTime instant

theorem berlin_differenceResolvedInYears_swap
    (first : LegacyCalendarLabel) (firstInstant : Instant)
    (second : LegacyCalendarLabel) (secondInstant : Instant) :
    (EuropeBerlinLegacyProfile.differenceResolvedInYears?
      first firstInstant second secondInstant).map (-·) =
    EuropeBerlinLegacyProfile.differenceResolvedInYears?
      second secondInstant first firstInstant := by
  exact berlin_signedWholePeriods_swap
    EuropeBerlinLegacyProfile.wholeYearsForward?
    first firstInstant second secondInstant

end A12Kernel
