import A12Kernel.Semantics.BerlinLegacyTimeZone

/-! # Versioned Europe/Berlin legacy timezone locks

These cases separate historical table lookup, post-1997 recurrence, gap rejection, smaller-offset overlap selection, and exact instant preservation. General model-zone dispatch, parsing, cells, and wall-day landing remain outside.
-/

namespace A12Kernel.Conformance.BerlinLegacyTimeZone

open A12Kernel

private def dateTime (year : Int) (month day hour minute second : Nat)
    (admissible :
      (LocalDateTime.ofYmdHms? year month day hour minute second).isSome) :
    LocalDateTime :=
  (LocalDateTime.ofYmdHms? year month day hour minute second).get admissible

/- The pinned historical table is complete, begins from flat CET, and changes at the exact first UTC boundary. -/
example :
    EuropeBerlinLegacyProfile.transitions.length = 62 ∧
      EuropeBerlinLegacyProfile.offsetSecondsAt?
          (dateTime 1900 1 1 0 0 0 (by native_decide)).resolveUtc = some 3600 ∧
      EuropeBerlinLegacyProfile.offsetSecondsAt?
          (dateTime 1916 4 30 21 59 59 (by native_decide)).resolveUtc = some 3600 ∧
      EuropeBerlinLegacyProfile.offsetSecondsAt?
          (dateTime 1916 4 30 22 0 0 (by native_decide)).resolveUtc = some 7200 := by
  native_decide

/- The historical table retains CEMT and the different pre-1996 autumn schedule. -/
example :
    EuropeBerlinLegacyProfile.offsetSecondsAt?
        (dateTime 1945 5 24 0 0 0 (by native_decide)).resolveUtc =
      some 10800 ∧
    EuropeBerlinLegacyProfile.offsetSecondsAt?
        (dateTime 1995 9 24 1 0 0 (by native_decide)).resolveUtc = some 3600 := by
  native_decide

/- The 1997 table boundary and 1998 recurrence are non-overlapping. -/
example :
    EuropeBerlinLegacyProfile.offsetSecondsAt?
        (dateTime 1997 10 26 0 59 59 (by native_decide)).resolveUtc =
      some 7200 ∧
    EuropeBerlinLegacyProfile.offsetSecondsAt?
        (dateTime 1997 10 26 1 0 0 (by native_decide)).resolveUtc = some 3600 ∧
    EuropeBerlinLegacyProfile.offsetSecondsAt?
        (dateTime 1998 3 29 1 0 0 (by native_decide)).resolveUtc = some 7200 := by
  native_decide

/- Modern fresh gaps fail and overlaps select the smaller standard offset in every recurrence year. -/
example :
    EuropeBerlinLegacyProfile.resolveLocal?
        (dateTime 2025 3 30 2 30 0 (by native_decide)) =
      none := by
  native_decide
example :
    EuropeBerlinLegacyProfile.resolveLocal?
        (dateTime 2025 10 26 2 30 0 (by native_decide)) =
      some ((dateTime 2025 10 26 2 30 0 (by native_decide)).resolveUtc.shiftHours (-1)) := by
  native_decide

/- Historical CEST-to-CEMT gaps reject fresh labels, while CEMT-to-CEST overlaps select the smaller after-offset. -/
example :
    EuropeBerlinLegacyProfile.resolveLocal?
        (dateTime 1945 5 24 2 30 0 (by native_decide)) = none := by
  native_decide
example :
    EuropeBerlinLegacyProfile.resolveLocal?
        (dateTime 1945 9 24 2 30 0 (by native_decide)) =
      some ((dateTime 1945 9 24 2 30 0 (by native_decide)).resolveUtc.shiftHours (-2)) := by
  native_decide

/- Chained instant arithmetic keeps the early-side identity instead of reparsing the rendered overlap label. -/
example :
    (EuropeBerlinLegacyProfile.resolveLocal?
        (dateTime 2024 10 27 1 30 0 (by native_decide))).map
          (fun instant => instant.shiftHours 1) ≠
      EuropeBerlinLegacyProfile.resolveLocal?
        (dateTime 2024 10 27 2 30 0 (by native_decide)) := by
  native_decide
example :
    (EuropeBerlinLegacyProfile.resolveLocal?
        (dateTime 2024 10 27 1 30 0 (by native_decide))).map
          (fun instant => instant.shiftHours 2) =
      EuropeBerlinLegacyProfile.resolveLocal?
        (dateTime 2024 10 27 2 30 0 (by native_decide)) := by
  native_decide

end A12Kernel.Conformance.BerlinLegacyTimeZone
