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

/- The adjusted landing is before 01:45, so one calendar day fits even though fewer than 86,400 elapsed seconds fit. -/
example :
    EuropeBerlinLegacyProfile.differenceInDays?
        (dateTime 2024 3 30 2 30 0 (by native_decide))
        (dateTime 2024 3 31 1 45 0 (by native_decide)) =
      some 1 := by
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

/- A forward fall-back landing chooses the earlier instant; fresh-label resolution would choose the later standard-time instant and count zero here. -/
example :
    EuropeBerlinLegacyProfile.differenceInDays?
        (dateTime 2024 10 26 2 30 0 (by native_decide))
        (dateTime 2024 10 27 2 15 0 (by native_decide)) =
      some 1 := by
  native_decide

/- The same no-overshoot rule survives the historical CEMT-to-CEST overlap. -/
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
