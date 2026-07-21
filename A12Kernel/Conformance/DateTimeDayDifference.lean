import A12Kernel.Semantics.DateTimeDayDifference

/-! # Finite Berlin 2024 calendar-day difference locks

These cases exercise only the declared spring-transition slice. They distinguish stateful legacy-calendar day landings from elapsed-seconds or proleptic wall-label quotients without claiming a general Berlin calendar.
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
    Berlin2024Profile.differenceInDays?
        (dateTime 2024 3 29 12 0 0 (by native_decide))
        (dateTime 2024 3 30 12 0 0 (by native_decide)) =
      some 1 := by
  native_decide

/- A fresh local label in the spring gap is rejected. -/
example :
    Berlin2024Profile.resolveLocal?
        (dateTime 2024 3 31 2 30 0 (by native_decide)) =
      none := by
  native_decide

/- Stateful day addition into the gap lands one hour earlier and retains minutes and seconds. -/
example :
    Berlin2024Profile.nextCalendarDay?
        (dateTime 2024 3 30 2 30 15 (by native_decide)) =
      some (dateTime 2024 3 31 1 30 15 (by native_decide)) := by
  native_decide

/- The adjusted landing is before 01:45, so one calendar day fits even though fewer than 86,400 elapsed seconds fit. -/
example :
    Berlin2024Profile.differenceInDays?
        (dateTime 2024 3 30 2 30 0 (by native_decide))
        (dateTime 2024 3 31 1 45 0 (by native_decide)) =
      some 1 := by
  native_decide

example :
    (do
      let first ← Berlin2024Profile.resolveLocal?
        (dateTime 2024 3 30 2 30 0 (by native_decide))
      let second ← Berlin2024Profile.resolveLocal?
        (dateTime 2024 3 31 1 45 0 (by native_decide))
      pure ((second.epochSecond - first.epochSecond).tdiv 86400)) =
      some 0 := by
  native_decide

/- Moving the endpoint just before the adjusted landing counts no complete calendar day. -/
example :
    Berlin2024Profile.differenceInDays?
        (dateTime 2024 3 30 2 30 0 (by native_decide))
        (dateTime 2024 3 31 1 29 59 (by native_decide)) =
      some 0 := by
  native_decide

/- Authored operand order controls the sign. -/
example :
    Berlin2024Profile.differenceInDays?
        (dateTime 2024 3 31 1 45 0 (by native_decide))
        (dateTime 2024 3 30 2 30 0 (by native_decide)) =
      some (-1) := by
  native_decide

/- The second step retains the first landing's adjusted 01:30 clock, so two days fit before 02:00 on April 1. -/
example :
    Berlin2024Profile.differenceInDays?
        (dateTime 2024 3 30 2 30 0 (by native_decide))
        (dateTime 2024 4 1 2 0 0 (by native_decide)) =
      some 2 := by
  native_decide

/- The bounded day-difference consumer fails closed outside its consecutive spring slice. -/
example :
    Berlin2024Profile.differenceInDays?
        (dateTime 2024 3 30 12 0 0 (by native_decide))
        (dateTime 2024 10 27 12 0 0 (by native_decide)) =
      none := by
  native_decide

end A12Kernel.Conformance.DateTimeDayDifference
