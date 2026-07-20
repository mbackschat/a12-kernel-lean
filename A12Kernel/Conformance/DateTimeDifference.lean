import A12Kernel.Semantics.DateTimeDifference

/-! # Resolved DateTime-difference executable locks

These cases start after both DateTime operands have been resolved to exact instants. They lock authored argument order, truncation toward zero, physical elapsed time across the selected Berlin overlap, and the non-additivity introduced by per-operation truncation.
-/

namespace A12Kernel.Conformance.DateTimeDifference

open A12Kernel

private def instant (epochSecond : Int) : Instant := { epochSecond }

private def dateTime (year : Int) (month day hour minute second : Nat)
    (admissible :
      (LocalDateTime.ofYmdHms? year month day hour minute second).isSome) :
    LocalDateTime :=
  (LocalDateTime.ofYmdHms? year month day hour minute second).get admissible

/- The positive 5 h 30 m 15 s span truncates independently in each unit. -/
example :
    (instant 0).difference .hours (instant 19815) = 5 := by
  native_decide

example :
    (instant 0).difference .minutes (instant 19815) = 330 := by
  native_decide

example :
    (instant 0).difference .seconds (instant 19815) = 19815 := by
  native_decide

/- Argument order is second minus first; negative fractions truncate toward zero, not toward minus infinity. -/
example :
    (instant 19815).difference .hours (instant 0) = -5 := by
  native_decide

example :
    (instant 19815).difference .minutes (instant 0) = -330 := by
  native_decide

example :
    (instant 19815).difference .seconds (instant 0) = -19815 := by
  native_decide

/- The selected Berlin autumn endpoints are three physical hours apart despite two wall-clock hours. -/
example :
    (do
      let first ← BerlinAutumn2024.resolveLocal?
        (dateTime 2024 10 27 1 30 0 (by native_decide))
      let second ← BerlinAutumn2024.resolveLocal?
        (dateTime 2024 10 27 3 30 0 (by native_decide))
      pure (first.difference .hours second)) =
        some 3 := by
  native_decide

/- A fresh ambiguous 02:30 selects the standard-side instant, 120 minutes after fresh 01:30. -/
example :
    (do
      let first ← BerlinAutumn2024.resolveLocal?
        (dateTime 2024 10 27 1 30 0 (by native_decide))
      let second ← BerlinAutumn2024.resolveLocal?
        (dateTime 2024 10 27 2 30 0 (by native_decide))
      pure (first.difference .minutes second)) =
        some 120 := by
  native_decide

/- Chained instant arithmetic reaches daylight-side 02:30, still 60 minutes before fresh standard-side 02:30. -/
example :
    (do
      let first ← BerlinAutumn2024.resolveLocal?
        (dateTime 2024 10 27 1 30 0 (by native_decide))
      let second ← BerlinAutumn2024.resolveLocal?
        (dateTime 2024 10 27 2 30 0 (by native_decide))
      pure ((first.shiftHours 1).difference .minutes second)) =
        some 60 := by
  native_decide

/- Per-operation truncation means differences cannot be added after independently rounding each segment. -/
example :
    (instant 0).difference .hours (instant 3599) +
        (instant 3599).difference .hours (instant 7198) ≠
      (instant 0).difference .hours (instant 7198) := by
  native_decide

end A12Kernel.Conformance.DateTimeDifference
