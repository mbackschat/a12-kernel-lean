import A12Kernel.Semantics.DateTimeDayDifference

/-! # Model-zone calendar-day difference locks

These cases exercise the concrete UTC and versioned Berlin profiles. They distinguish stateful legacy-calendar landings from elapsed-seconds or proleptic wall-label quotients, including historical gap/overlap behavior and bounded long-range seeding.
-/

namespace A12Kernel.Conformance.DateTimeDayDifference

open A12Kernel

private def dateTime (year : Int) (month day hour minute second : Nat)
    (admissible :
      (LocalDateTime.ofYmdHms? year month day hour minute second).isSome) :
    LocalDateTime :=
  (LocalDateTime.ofYmdHms? year month day hour minute second).get admissible

private def berlinDayLanding? (source : LocalDateTime) (days : Int) := do
  let sourceInstant ← EuropeBerlinLegacyProfile.resolveLocal? source
  EuropeBerlinLegacyProfile.calendarDayLanding? source sourceInstant days

/- An ordinary consecutive day with the same clock counts once. -/
example :
    EuropeBerlinLegacyProfile.differenceInDays?
        (dateTime 2024 3 29 12 0 0 (by native_decide))
        (dateTime 2024 3 30 12 0 0 (by native_decide)) =
      some 1 := by
  native_decide

/- A fresh local label in the spring gap is rejected. -/
example :
    EuropeBerlinLegacyProfile.resolveLocal?
        (dateTime 2024 3 31 2 30 0 (by native_decide)) =
      none := by
  native_decide

/- A source carrying the post-transition offset into a backward day landing re-fits the nominal gap label to the post-gap wall clock. -/
example :
    berlinDayLanding?
        (dateTime 2024 4 1 2 30 0 (by native_decide)) (-1) =
      some (
        dateTime 2024 3 31 3 30 0 (by native_decide),
        { epochMillis := 1711848600000 }) := by
  native_decide

/- A long forward addition carries the source's standard-time offset into the repeated target label. Direction alone would choose the wrong instant. -/
example :
    berlinDayLanding?
        (dateTime 1916 3 1 0 0 0 (by native_decide)) 214 =
      some (
        dateTime 1916 10 1 0 0 0 (by native_decide),
        { epochMillis := -1680483600000 }) := by
  native_decide

/- Long landings into the modern spring gap retain the source offset: the standard-time source re-fits forward to 03:30, while the daylight-time source keeps the first 01:30 candidate when moving backward. -/
example :
    berlinDayLanding?
        (dateTime 2023 8 31 2 30 0 (by native_decide)) 213 =
      some (
        dateTime 2024 3 31 3 30 0 (by native_decide),
        { epochMillis := 1711848600000 }) ∧
    berlinDayLanding?
        (dateTime 2024 11 30 2 30 0 (by native_decide)) (-244) =
      some (
        dateTime 2024 3 31 1 30 0 (by native_decide),
        { epochMillis := 1711845000000 }) := by
  native_decide

/- If re-fitting a gap candidate would change the target civil date, Calendar keeps the first source-offset candidate. -/
example :
    berlinDayLanding?
        (dateTime 1916 5 1 23 30 0 (by native_decide)) (-1) =
      some (
        dateTime 1916 4 30 22 30 0 (by native_decide),
        { epochMillis := -1693708200000 }) := by
  native_decide

/- `Calendar.YEAR` is not forward day mutation. At an overlap it chooses the later
   standard-time instant, and at a gap it normalizes to the post-gap wall label. -/
example :
    (do
      let source :=
        dateTime 1915 10 1 0 0 0 (by native_decide)
      let sourceInstant ←
        EuropeBerlinLegacyProfile.resolveLocal? source
      EuropeBerlinLegacyProfile.calendarYearLanding?
        source sourceInstant 1) =
      some (
        dateTime 1916 10 1 0 0 0 (by native_decide),
        { epochMillis := -1680483600000 }) ∧
    (do
      let source :=
        dateTime 1915 4 30 23 30 0 (by native_decide)
      let sourceInstant ←
        EuropeBerlinLegacyProfile.resolveLocal? source
      EuropeBerlinLegacyProfile.calendarYearLanding?
        source sourceInstant 1) =
      some (
        dateTime 1916 5 1 0 30 0 (by native_decide),
        { epochMillis := -1693704600000 }) := by
  native_decide

/- Day and year mutation are not interchangeable landing policies. The day source carries CEST into the repeated label; year compute-time resolution selects CET. -/
example :
    (do
      let daySource :=
        dateTime 1916 9 30 0 0 0 (by native_decide)
      let yearSource :=
        dateTime 1915 10 1 0 0 0 (by native_decide)
      let yearInstant ←
        EuropeBerlinLegacyProfile.resolveLocal? yearSource
      let dayLanding ← berlinDayLanding? daySource 1
      let yearLanding ←
        EuropeBerlinLegacyProfile.calendarYearLanding?
          yearSource yearInstant 1
      pure (dayLanding.2 != yearLanding.2)) =
      some true := by
  native_decide

/- The adjusted landing is before 01:45, so one calendar day fits even though fewer than 86,400 elapsed seconds fit. -/
example :
    EuropeBerlinLegacyProfile.differenceInDays?
        (dateTime 2024 3 30 2 30 0 (by native_decide))
        (dateTime 2024 3 31 1 45 0 (by native_decide)) =
      some 1 := by
  native_decide

/- The source-offset rule affects the public count once a multi-day seed crosses both offset seasons. -/
example :
    EuropeBerlinLegacyProfile.differenceInDays?
        (dateTime 2023 4 1 2 30 0 (by native_decide))
        (dateTime 2024 4 5 2 30 0 (by native_decide)) =
      some 369 := by
  native_decide

/- Calendar field mutation preserves the source millisecond. The exact endpoint at the same whole-second label is therefore still too early for one complete day. -/
example :
    (do
      let firstLabel :=
        dateTime 2024 6 1 2 30 0 (by native_decide)
      let secondLabel :=
        dateTime 2024 6 2 2 30 0 (by native_decide)
      let first ← EuropeBerlinLegacyProfile.resolveLocal? firstLabel
      let second ← EuropeBerlinLegacyProfile.resolveLocal? secondLabel
      EuropeBerlinLegacyProfile.differenceResolvedInDays?
        firstLabel { epochMillis := first.epochMillis + 500 }
        secondLabel second) =
      some 0 := by
  native_decide

/- Month mutation shares the sign-independent compute-time resolver: a nominal gap normalizes to the post-gap label. -/
example :
    (do
      let source :=
        dateTime 2024 1 31 2 30 0 (by native_decide)
      let sourceInstant ←
        EuropeBerlinLegacyProfile.resolveLocal? source
      EuropeBerlinLegacyProfile.calendarMonthLanding?
        source sourceInstant 2) =
      some (
        dateTime 2024 3 31 3 30 0 (by native_decide),
        { epochMillis := 1711848600000 }) := by
  native_decide

/- A normalized intermediate month can already pass an endpoint whose calendar coordinate is two months away. The completed-month search must test fresh candidates from its year lower bound rather than jumping to the coordinate candidate. -/
example :
    (do
      let firstLabel :=
        dateTime 1916 3 30 23 30 0 (by native_decide)
      let secondLabel :=
        dateTime 1916 5 1 0 0 0 (by native_decide)
      let first ← EuropeBerlinLegacyProfile.resolveLocal? firstLabel
      let second ← EuropeBerlinLegacyProfile.resolveLocal? secondLabel
      EuropeBerlinLegacyProfile.differenceResolvedInMonths?
        firstLabel first secondLabel second) =
      some 0 := by
  native_decide

/- The leap-to-nonleap February-28 branch clears the entire clock even for a negative year shift. -/
example :
    (do
      let source :=
        dateTime 2000 2 28 2 30 0 (by native_decide)
      let sourceInstant ←
        EuropeBerlinLegacyProfile.resolveLocal? source
      EuropeBerlinLegacyProfile.calendarYearLanding?
        source sourceInstant (-1)) =
      some (
        dateTime 1999 2 28 0 0 0 (by native_decide),
        { epochMillis := 920156400000 }) := by
  native_decide

example :
    (do
      let first ← EuropeBerlinLegacyProfile.resolveLocal?
        (dateTime 2024 3 30 2 30 0 (by native_decide))
      let second ← EuropeBerlinLegacyProfile.resolveLocal?
        (dateTime 2024 3 31 1 45 0 (by native_decide))
      pure ((second.epochMillis - first.epochMillis).tdiv 86400000)) =
      some 0 := by
  native_decide

/- Moving the endpoint just before the adjusted landing counts no complete calendar day. -/
example :
    EuropeBerlinLegacyProfile.differenceInDays?
        (dateTime 2024 3 30 2 30 0 (by native_decide))
        (dateTime 2024 3 31 1 29 59 (by native_decide)) =
      some 0 := by
  native_decide

/- Authored operand order controls the sign. -/
example :
    EuropeBerlinLegacyProfile.differenceInDays?
        (dateTime 2024 3 31 1 45 0 (by native_decide))
        (dateTime 2024 3 30 2 30 0 (by native_decide)) =
      some (-1) := by
  native_decide

/- The second step retains the first landing's adjusted 01:30 clock, so two days fit before 02:00 on April 1. -/
example :
    EuropeBerlinLegacyProfile.differenceInDays?
        (dateTime 2024 3 30 2 30 0 (by native_decide))
        (dateTime 2024 4 1 2 0 0 (by native_decide)) =
      some 2 := by
  native_decide

/- The general profile closes the old finite-slice rejection. -/
example :
    EuropeBerlinLegacyProfile.differenceInDays?
        (dateTime 2024 3 30 12 0 0 (by native_decide))
        (dateTime 2024 10 27 12 0 0 (by native_decide)) =
      some 211 := by
  native_decide

/- The source carries its larger daylight offset into the overlap, choosing the earlier instant; fresh-label resolution would choose the later standard-time instant and count zero here. -/
example :
    EuropeBerlinLegacyProfile.differenceInDays?
        (dateTime 2024 10 26 2 30 0 (by native_decide))
        (dateTime 2024 10 27 2 15 0 (by native_decide)) =
      some 1 := by
  native_decide

/- The three-offset candidate set is load-bearing at the historical CEMT-to-CEST overlap: the source carries CEMT into the repeated target label. -/
example :
    EuropeBerlinLegacyProfile.differenceInDays?
        (dateTime 1945 9 23 2 30 0 (by native_decide))
        (dateTime 1945 9 24 2 15 0 (by native_decide)) =
      some 1 := by
  native_decide

/- A 24-year interval exercises the whole-year × 365 seed plus six residual leap-day steps. -/
example :
    EuropeBerlinLegacyProfile.differenceInDays?
        (dateTime 2000 1 1 12 0 0 (by native_decide))
        (dateTime 2024 1 1 12 0 0 (by native_decide)) =
      some 8766 := by
  native_decide

/- An endpoint before the anniversary decrements the civil-year candidate before seeding. Using the raw four-year difference would start beyond this endpoint. -/
example :
    EuropeBerlinLegacyProfile.differenceInDays?
        (dateTime 2020 6 15 12 0 0 (by native_decide))
        (dateTime 2024 6 10 12 0 0 (by native_decide)) =
      some 1456 := by
  native_decide

/- The bulk lower-bound jump must not inherit a clock adjustment from an intervening spring gap. The legacy year landing clears this leap-to-nonleap February-28 clock, so the one-year seed is admitted; a naïve day-by-day scan would cross the 2000 spring gap and count 366 after changing 02:30 to 01:30. -/
example :
    EuropeBerlinLegacyProfile.differenceInDays?
        (dateTime 2000 2 28 2 30 0 (by native_decide))
        (dateTime 2001 2 28 2 0 0 (by native_decide)) =
      some 365 := by
  native_decide

/- Concrete profile selection distinguishes aliases from an unsupported legal zone before evaluation. -/
example :
    ModelZone.ConcreteProfile.ofId? "UTC" =
      some .utc ∧
    ModelZone.ConcreteProfile.ofId? "GMT" =
      some .utc ∧
    ModelZone.ConcreteProfile.ofId? "Europe/Berlin" =
      some .europeBerlin ∧
    ModelZone.ConcreteProfile.ofId? "Pacific/Apia" =
      none := by
  native_decide

/- The typed concrete-profile consumer preserves UTC without re-running string dispatch. -/
example :
    ModelZone.ConcreteProfile.differenceInDays? .utc
        (dateTime 2024 3 30 2 30 0 (by native_decide))
        (dateTime 2024 3 31 1 45 0 (by native_decide)) =
      some 0 := by
  native_decide

/- The compatibility wrapper still refuses an unsupported profile rather than extrapolating Berlin. -/
example :
    ModelZone.concreteDifferenceInDays? "Pacific/Apia"
        (dateTime 2011 12 29 12 0 0 (by native_decide))
        (dateTime 2011 12 31 12 0 0 (by native_decide)) =
      none := by
  native_decide

end A12Kernel.Conformance.DateTimeDayDifference
