import A12Kernel.Semantics.BerlinLegacyCalendarArithmetic

/-! # Berlin legacy calendar arithmetic locks

These cases separate source-offset day mutation from sign-independent month/year compute-time resolution, exact millisecond identity, February correction, and the fresh-source completed-month search.
-/

namespace A12Kernel.Conformance.BerlinLegacyCalendarArithmetic

open A12Kernel

private def dateTime (year : Int) (month day hour minute second : Nat)
    (admissible :
      (LocalDateTime.ofYmdHms? year month day hour minute second).isSome) :
    LocalDateTime :=
  (LocalDateTime.ofYmdHms? year month day hour minute second).get admissible

private def berlinDayLanding? (source : LocalDateTime) (days : Int) := do
  let sourceInstant ← EuropeBerlinLegacyProfile.resolveLocal? source
  EuropeBerlinLegacyProfile.calendarDayLanding? source sourceInstant days

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

/- Long landings into the modern spring gap retain the source offset in both directions. -/
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

/- If re-fitting a gap candidate would change the target civil date, the first source-offset candidate remains authoritative. -/
example :
    berlinDayLanding?
        (dateTime 1916 5 1 23 30 0 (by native_decide)) (-1) =
      some (
        dateTime 1916 4 30 22 30 0 (by native_decide),
        { epochMillis := -1693708200000 }) := by
  native_decide

/- Year mutation uses sign-independent compute-time resolution at both an overlap and a gap. -/
example :
    (do
      let source := dateTime 1915 10 1 0 0 0 (by native_decide)
      let sourceInstant ← EuropeBerlinLegacyProfile.resolveLocal? source
      EuropeBerlinLegacyProfile.calendarYearLanding?
        source sourceInstant 1) =
      some (
        dateTime 1916 10 1 0 0 0 (by native_decide),
        { epochMillis := -1680483600000 }) ∧
    (do
      let source := dateTime 1915 4 30 23 30 0 (by native_decide)
      let sourceInstant ← EuropeBerlinLegacyProfile.resolveLocal? source
      EuropeBerlinLegacyProfile.calendarYearLanding?
        source sourceInstant 1) =
      some (
        dateTime 1916 5 1 0 30 0 (by native_decide),
        { epochMillis := -1693704600000 }) := by
  native_decide

/- Day and year mutation are not interchangeable landing policies. -/
example :
    (do
      let daySource := dateTime 1916 9 30 0 0 0 (by native_decide)
      let yearSource := dateTime 1915 10 1 0 0 0 (by native_decide)
      let yearInstant ← EuropeBerlinLegacyProfile.resolveLocal? yearSource
      let dayLanding ← berlinDayLanding? daySource 1
      let yearLanding ←
        EuropeBerlinLegacyProfile.calendarYearLanding?
          yearSource yearInstant 1
      pure (dayLanding.2 != yearLanding.2)) =
      some true := by
  native_decide

/- Month mutation shares the sign-independent compute-time resolver: a nominal gap normalizes to the post-gap label. -/
example :
    (do
      let source := dateTime 2024 1 31 2 30 0 (by native_decide)
      let sourceInstant ← EuropeBerlinLegacyProfile.resolveLocal? source
      EuropeBerlinLegacyProfile.calendarMonthLanding?
        source sourceInstant 2) =
      some (
        dateTime 2024 3 31 3 30 0 (by native_decide),
        { epochMillis := 1711848600000 }) := by
  native_decide

/- An intermediate normalized month can overshoot before the final calendar coordinate is reached. -/
example :
    (do
      let firstLabel := dateTime 1916 3 30 23 30 0 (by native_decide)
      let secondLabel := dateTime 1916 5 1 0 0 0 (by native_decide)
      let first ← EuropeBerlinLegacyProfile.resolveLocal? firstLabel
      let second ← EuropeBerlinLegacyProfile.resolveLocal? secondLabel
      EuropeBerlinLegacyProfile.differenceResolvedInMonths?
        firstLabel first secondLabel second) =
      some 0 := by
  native_decide

/- The leap-to-nonleap February-28 branch clears the entire clock even for a negative year shift. -/
example :
    (do
      let source := dateTime 2000 2 28 2 30 0 (by native_decide)
      let sourceInstant ← EuropeBerlinLegacyProfile.resolveLocal? source
      EuropeBerlinLegacyProfile.calendarYearLanding?
        source sourceInstant (-1)) =
      some (
        dateTime 1999 2 28 0 0 0 (by native_decide),
        { epochMillis := 920156400000 }) := by
  native_decide

end A12Kernel.Conformance.BerlinLegacyCalendarArithmetic
