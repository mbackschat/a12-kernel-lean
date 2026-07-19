import A12Kernel.Semantics.DateTime

/-! # DateTime conformance

Executable separators for decoded, whole-second local DateTime resolution under UTC, exact whole-hour shifting in instant space, and one fixed Berlin autumn-overlap risk slice. Parsing, formats, numeric-to-hour conversion, general zones, cells, and target admission remain outside this capsule.
-/

namespace A12Kernel

private def civilDate (year : Int) (month day : Nat)
    (real : (CivilDate.ofYmd? year month day).isSome) :
    CivilDate :=
  (CivilDate.ofYmd? year month day).get real

private def dateTime (year : Int) (month day hour minute second : Nat)
    (admissible : (LocalDateTime.ofYmdHms? year month day hour minute second).isSome) :
    LocalDateTime :=
  (LocalDateTime.ofYmdHms? year month day hour minute second).get admissible

/- Civil successor is calendar-aware and advances the scalar day coordinate exactly once. -/
example :
    (civilDate 2024 2 28 (by native_decide)).next? =
      some (civilDate 2024 2 29 (by native_decide)) := by
  native_decide
example :
    (civilDate 2024 2 29 (by native_decide)).next? =
      some (civilDate 2024 3 1 (by native_decide)) := by
  native_decide
example :
    (civilDate 1900 2 28 (by native_decide)).next? =
      some (civilDate 1900 3 1 (by native_decide)) := by
  native_decide
example :
    (civilDate 2023 4 30 (by native_decide)).next? =
      some (civilDate 2023 5 1 (by native_decide)) := by
  native_decide
example :
    (civilDate 1999 12 31 (by native_decide)).next? =
      some (civilDate 2000 1 1 (by native_decide)) := by
  native_decide
example :
    (civilDate 2024 2 29 (by native_decide)).next?.map
        CivilDate.unixEpochDay =
      some ((civilDate 2024 2 29 (by native_decide)).unixEpochDay + 1) := by
  native_decide

/- Decoded clock values enforce the exact whole-second bounds. -/
example : (TimeOfDay.ofHms? 0 0 0).isSome = true := by native_decide
example : (TimeOfDay.ofHms? 23 59 59).isSome = true := by native_decide
example : (TimeOfDay.ofHms? 24 0 0).isNone = true := by native_decide
example : (TimeOfDay.ofHms? 12 60 0).isNone = true := by native_decide
example : (TimeOfDay.ofHms? 12 34 60).isNone = true := by native_decide
example : (LocalDateTime.ofYmdHms? 1583 10 16 0 0 0).isSome = true := by native_decide
example : (LocalDateTime.ofYmdHms? 1583 10 15 23 59 59).isNone = true := by native_decide
example : (LocalDateTime.ofYmdHms? 2024 2 30 12 0 0).isNone = true := by native_decide
example : (LocalDateTime.ofYmdHms? 2024 1 1 24 0 0).isNone = true := by native_decide

/- UTC resolution uses the Unix epoch only as an origin for scalar instant identity. -/
example :
    (dateTime 1970 1 1 0 0 0 (by native_decide)).resolveUtc.epochSecond = 0 := by
  native_decide
example :
    (dateTime 1969 12 31 23 59 59 (by native_decide)).resolveUtc.epochSecond = -1 := by
  native_decide

/- Strict local chronology is preserved by UTC resolution across seconds, days, years, and leap days. -/
example :
    (dateTime 2024 1 1 0 0 0 (by native_decide)).Before
      (dateTime 2024 1 1 0 0 1 (by native_decide)) := by
  native_decide
example :
    (dateTime 2023 12 31 23 59 59 (by native_decide)).Before
      (dateTime 2024 1 1 0 0 0 (by native_decide)) := by
  native_decide
example :
    (dateTime 2024 2 29 23 59 59 (by native_decide)).Before
      (dateTime 2024 3 1 0 0 0 (by native_decide)) := by
  native_decide
example :
    ¬(dateTime 2024 1 1 0 0 1 (by native_decide)).Before
      (dateTime 2024 1 1 0 0 0 (by native_decide)) := by
  native_decide
example :
    (dateTime 2023 12 31 23 59 59 (by native_decide)).resolveUtc.epochSecond <
      (dateTime 2024 1 1 0 0 0 (by native_decide)).resolveUtc.epochSecond := by
  native_decide

/- Whole-hour shifting is instant-in/instant-out and carries over calendar boundaries. -/
example :
    (dateTime 2009 1 30 23 0 0 (by native_decide)).resolveUtc.shiftHours 2 =
      (dateTime 2009 1 31 1 0 0 (by native_decide)).resolveUtc := by
  native_decide
example :
    (dateTime 2009 1 30 12 0 0 (by native_decide)).resolveUtc.shiftHours 48 =
      (dateTime 2009 2 1 12 0 0 (by native_decide)).resolveUtc := by
  native_decide
example :
    (dateTime 2024 2 29 23 30 45 (by native_decide)).resolveUtc.shiftHours 2 =
      (dateTime 2024 3 1 1 30 45 (by native_decide)).resolveUtc := by
  native_decide
example :
    (dateTime 1900 2 28 23 30 45 (by native_decide)).resolveUtc.shiftHours 2 =
      (dateTime 1900 3 1 1 30 45 (by native_decide)).resolveUtc := by
  native_decide
example :
    (dateTime 2000 2 29 23 30 45 (by native_decide)).resolveUtc.shiftHours 2 =
      (dateTime 2000 3 1 1 30 45 (by native_decide)).resolveUtc := by
  native_decide
example :
    (dateTime 2023 4 30 23 30 45 (by native_decide)).resolveUtc.shiftHours 1 =
      (dateTime 2023 5 1 0 30 45 (by native_decide)).resolveUtc := by
  native_decide
example :
    (dateTime 2000 12 31 23 30 45 (by native_decide)).resolveUtc.shiftHours 2 =
      (dateTime 2001 1 1 1 30 45 (by native_decide)).resolveUtc := by
  native_decide
example :
    (dateTime 1900 12 31 23 30 45 (by native_decide)).resolveUtc.shiftHours 2 =
      (dateTime 1901 1 1 1 30 45 (by native_decide)).resolveUtc := by
  native_decide
example :
    (dateTime 2000 1 1 0 30 0 (by native_decide)).resolveUtc.shiftHours (-1) =
      (dateTime 1999 12 31 23 30 0 (by native_decide)).resolveUtc := by
  native_decide

/- UTC has no autumn fold: the equal-looking fresh local value denotes the shifted instant. -/
example :
    (dateTime 2024 10 27 1 30 0 (by native_decide)).resolveUtc.shiftHours 1 =
      (dateTime 2024 10 27 2 30 0 (by native_decide)).resolveUtc := by
  native_decide
example :
    ((dateTime 2024 10 27 1 30 0 (by native_decide)).resolveUtc.shiftHours 1).shiftHours 1 =
      (dateTime 2024 10 27 3 30 0 (by native_decide)).resolveUtc := by
  native_decide

/- A same-date hour wrap is not a substitute for instant arithmetic. -/
example :
    (dateTime 2009 1 30 23 0 0 (by native_decide)).resolveUtc.shiftHours 2 ≠
      (dateTime 2009 1 30 1 0 0 (by native_decide)).resolveUtc := by
  native_decide

/- Runtime shifting can cross below the value floor; a later consumer decides whether to admit the resulting instant as a field value. -/
example :
    (dateTime 1583 10 16 0 0 0 (by native_decide)).resolveUtc.shiftHours (-1) =
      { epochSecond :=
          (dateTime 1583 10 16 0 0 0 (by native_decide)).resolveUtc.epochSecond - 3600 } := by
  native_decide

/- The selected Berlin autumn slice distinguishes fresh wall-time parsing from chained instant arithmetic. -/
example :
    BerlinAutumn2024.resolveLocal?
        (dateTime 2024 10 27 1 30 0 (by native_decide)) =
      some { epochSecond := 1729985400 } := by
  native_decide
example :
    BerlinAutumn2024.resolveLocal?
        (dateTime 2024 10 27 2 30 0 (by native_decide)) =
      some { epochSecond := 1729992600 } := by
  native_decide
example :
    (BerlinAutumn2024.resolveLocal?
        (dateTime 2024 10 27 1 30 0 (by native_decide))).map
          (fun instant => instant.shiftHours 1) =
      some { epochSecond := 1729989000 } := by
  native_decide
example :
    (BerlinAutumn2024.resolveLocal?
        (dateTime 2024 10 27 1 30 0 (by native_decide))).map
          (fun instant => instant.shiftHours 1) ≠
      BerlinAutumn2024.resolveLocal?
        (dateTime 2024 10 27 2 30 0 (by native_decide)) := by
  native_decide
example :
    (BerlinAutumn2024.resolveLocal?
        (dateTime 2024 10 27 1 30 0 (by native_decide))).map
          (fun instant => instant.shiftHours 2) =
      BerlinAutumn2024.resolveLocal?
        (dateTime 2024 10 27 2 30 0 (by native_decide)) := by
  native_decide

/- The offset changes exactly at 02:00; unsupported dates fail closed. -/
example :
    BerlinAutumn2024.resolveLocal?
        (dateTime 2024 10 27 1 59 59 (by native_decide)) =
      some ((dateTime 2024 10 27 1 59 59 (by native_decide)).resolveUtc.shiftHours (-2)) := by
  native_decide
example :
    BerlinAutumn2024.resolveLocal?
        (dateTime 2024 10 27 2 0 0 (by native_decide)) =
      some ((dateTime 2024 10 27 2 0 0 (by native_decide)).resolveUtc.shiftHours (-1)) := by
  native_decide
example :
    BerlinAutumn2024.resolveLocal?
        (dateTime 2024 10 26 2 30 0 (by native_decide)) =
      none := by
  native_decide
example :
    BerlinAutumn2024.resolveLocal?
        (dateTime 2024 3 31 2 30 0 (by native_decide)) =
      none := by
  native_decide
example :
    BerlinAutumn2024.resolveLocal?
        (dateTime 2025 10 26 2 30 0 (by native_decide)) =
      none := by
  native_decide

end A12Kernel
