import A12Kernel.Semantics.DateTimeDayDifference

/-! # Concrete Berlin calendar-day difference laws

These laws characterize the signed partial API over the pinned versioned Berlin profile. They do not claim correspondence for another zone or calendar basis.
-/

namespace A12Kernel

/-- A Berlin label is zero calendar days from itself exactly when the profile admits it. -/
theorem berlin_differenceInDays_self (dateTime : LocalDateTime) :
    EuropeBerlinLegacyProfile.differenceInDays? dateTime dateTime =
      (EuropeBerlinLegacyProfile.resolveLocal? dateTime).map fun _ => 0 := by
  cases resolved : EuropeBerlinLegacyProfile.resolveLocal? dateTime <;>
    simp [EuropeBerlinLegacyProfile.differenceInDays?, resolved]

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
              secondResolved, before, notAfter]
          · by_cases after : secondInstant.epochMillis < firstInstant.epochMillis
            · simp [EuropeBerlinLegacyProfile.differenceInDays?, firstResolved,
                secondResolved, before, after, Function.comp_def]
            · simp [EuropeBerlinLegacyProfile.differenceInDays?, firstResolved,
                secondResolved, before, after]

end A12Kernel
