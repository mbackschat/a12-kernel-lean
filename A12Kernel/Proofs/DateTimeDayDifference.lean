import A12Kernel.Semantics.DateTimeDayDifference

/-! # Concrete Berlin calendar-day difference laws

These laws characterize the signed partial API over the pinned versioned Berlin profile. They do not claim correspondence for another zone or calendar basis.
-/

namespace A12Kernel

/-- A zero-day Berlin landing preserves both the decoded local state and its already
    selected exact instant; it never re-resolves an ambiguous wall label. -/
@[simp] theorem berlin_calendarDayLanding_zero
    (dateTime : LocalDateTime) (instant : Instant) :
    EuropeBerlinLegacyProfile.calendarDayLanding?
        dateTime instant 0 =
      some (dateTime, instant) := by
  simp [EuropeBerlinLegacyProfile.calendarDayLanding?]

/-- A zero-day backward Berlin landing preserves the already selected exact instant just like the forward zero case; neither direction re-resolves an ambiguous wall label. -/
@[simp] theorem berlin_calendarDayLandingBackward_zero
    (dateTime : LocalDateTime) (instant : Instant) :
    EuropeBerlinLegacyProfile.calendarDayLandingBackward?
        dateTime instant 0 =
      some (dateTime, instant) := by
  simp [EuropeBerlinLegacyProfile.calendarDayLandingBackward?]

/-- An already resolved Berlin value is zero calendar days from itself without re-resolving its possibly ambiguous local label. -/
theorem berlin_differenceResolvedInDays_self
    (dateTime : LocalDateTime) (instant : Instant) :
    EuropeBerlinLegacyProfile.differenceResolvedInDays?
        dateTime instant dateTime instant =
      some 0 := by
  simp [EuropeBerlinLegacyProfile.differenceResolvedInDays?]

/-- Swapping two already resolved Berlin operands negates the result while preserving their exact overlap identities. -/
theorem berlin_differenceResolvedInDays_swap
    (first : LocalDateTime) (firstInstant : Instant)
    (second : LocalDateTime) (secondInstant : Instant) :
    (EuropeBerlinLegacyProfile.differenceResolvedInDays?
      first firstInstant second secondInstant).map (-·) =
    EuropeBerlinLegacyProfile.differenceResolvedInDays?
      second secondInstant first firstInstant := by
  by_cases before : firstInstant.epochMillis < secondInstant.epochMillis
  · have notAfter : ¬secondInstant.epochMillis < firstInstant.epochMillis := by
      omega
    simp [EuropeBerlinLegacyProfile.differenceResolvedInDays?,
      before, notAfter]
  · by_cases after : secondInstant.epochMillis < firstInstant.epochMillis
    · simp [EuropeBerlinLegacyProfile.differenceResolvedInDays?,
        before, after, Function.comp_def]
    · simp [EuropeBerlinLegacyProfile.differenceResolvedInDays?,
        before, after]

/-- A Berlin label is zero calendar days from itself exactly when the profile admits it. -/
theorem berlin_differenceInDays_self (dateTime : LocalDateTime) :
    EuropeBerlinLegacyProfile.differenceInDays? dateTime dateTime =
      (EuropeBerlinLegacyProfile.resolveLocal? dateTime).map fun _ => 0 := by
  cases resolved : EuropeBerlinLegacyProfile.resolveLocal? dateTime <;>
    simp [EuropeBerlinLegacyProfile.differenceInDays?,
      EuropeBerlinLegacyProfile.differenceResolvedInDays?, resolved]

/-- Swapping two Berlin operands negates the signed calendar-day result; gap inputs remain symmetrically rejected. -/
theorem berlin_differenceInDays_swap
    (first second : LocalDateTime) :
    (EuropeBerlinLegacyProfile.differenceInDays? first second).map
        (fun days => -days) =
      EuropeBerlinLegacyProfile.differenceInDays? second first := by
  cases firstResolved : EuropeBerlinLegacyProfile.resolveLocal? first with
  | none =>
      simp [EuropeBerlinLegacyProfile.differenceInDays?, firstResolved]
  | some firstInstant =>
      cases secondResolved : EuropeBerlinLegacyProfile.resolveLocal? second with
      | none =>
          simp [EuropeBerlinLegacyProfile.differenceInDays?, firstResolved,
            secondResolved]
      | some secondInstant =>
          by_cases before : firstInstant.epochMillis < secondInstant.epochMillis
          · have notAfter : ¬secondInstant.epochMillis < firstInstant.epochMillis := by
              omega
            simp [EuropeBerlinLegacyProfile.differenceInDays?, firstResolved,
              EuropeBerlinLegacyProfile.differenceResolvedInDays?,
              secondResolved, before, notAfter]
          · by_cases after : secondInstant.epochMillis < firstInstant.epochMillis
            · simp [EuropeBerlinLegacyProfile.differenceInDays?, firstResolved,
                EuropeBerlinLegacyProfile.differenceResolvedInDays?,
                secondResolved, before, after, Function.comp_def]
            · simp [EuropeBerlinLegacyProfile.differenceInDays?, firstResolved,
                EuropeBerlinLegacyProfile.differenceResolvedInDays?,
                secondResolved, before, after]

end A12Kernel
