import A12Kernel.Semantics.DateTimeDayDifference

/-! # Finite Berlin 2024 calendar-day difference laws

These laws characterize only the declared spring-transition profile. They do not widen its date domain or claim correspondence for another zone, year, or calendar basis.
-/

namespace A12Kernel

/-- A spring-slice label is zero calendar days from itself exactly when the general Berlin resolver admits it. -/
theorem berlin2024_differenceInDays_self (dateTime : LocalDateTime) :
    Berlin2024Profile.differenceInDays? dateTime dateTime =
      if Berlin2024Profile.SpringSupported dateTime then
        (EuropeBerlinLegacyProfile.resolveLocal? dateTime).map fun _ => 0
      else
        none := by
  by_cases spring : Berlin2024Profile.SpringSupported dateTime
  · cases resolved : EuropeBerlinLegacyProfile.resolveLocal? dateTime <;>
      simp [Berlin2024Profile.differenceInDays?, spring, resolved]
  · simp [Berlin2024Profile.differenceInDays?, spring]

/-- Swapping two admitted spring-profile operands negates the signed calendar-day result; unsupported and gap inputs remain symmetrically rejected. -/
theorem berlin2024_differenceInDays_swap
    (first second : LocalDateTime) :
    (Berlin2024Profile.differenceInDays? first second).map
        (fun days => -days) =
      Berlin2024Profile.differenceInDays? second first := by
  by_cases firstSpring : Berlin2024Profile.SpringSupported first
  · by_cases secondSpring : Berlin2024Profile.SpringSupported second
    · cases firstResolved : EuropeBerlinLegacyProfile.resolveLocal? first with
      | none =>
          simp [Berlin2024Profile.differenceInDays?, firstSpring,
            secondSpring, firstResolved]
      | some firstInstant =>
          cases secondResolved : EuropeBerlinLegacyProfile.resolveLocal? second with
          | none =>
              simp [Berlin2024Profile.differenceInDays?, firstSpring,
                secondSpring, firstResolved, secondResolved]
          | some secondInstant =>
              by_cases before : firstInstant.epochMillis < secondInstant.epochMillis
              · have notAfter : ¬secondInstant.epochMillis < firstInstant.epochMillis := by
                  omega
                simp [Berlin2024Profile.differenceInDays?, firstSpring,
                  secondSpring, firstResolved, secondResolved, before,
                  notAfter]
              · by_cases after : secondInstant.epochMillis < firstInstant.epochMillis
                · simp [Berlin2024Profile.differenceInDays?, firstSpring,
                    secondSpring, firstResolved, secondResolved, before,
                    after]
                · simp [Berlin2024Profile.differenceInDays?, firstSpring,
                    secondSpring, firstResolved, secondResolved, before,
                    after]
    · simp [Berlin2024Profile.differenceInDays?, firstSpring,
        secondSpring]
  · simp [Berlin2024Profile.differenceInDays?, firstSpring]

end A12Kernel
