import A12Kernel.Semantics.ConstructedDateShift
import A12Kernel.Semantics.DateConstructionNumeric
import A12Kernel.Semantics.CivilDateCoordinate

/-! # Hybrid-calendar day coordinate

This capsule supplies one bounded whole-day coordinate for the default October 1582 legacy-calendar cutover, which static admission of a date constant still uses (spec/05 §1). Gregorian labels from 1582-10-15 onward reuse the existing civil coordinate; earlier labels use a four-year Julian cycle aligned so 1582-10-04 immediately precedes 1582-10-15.

Runtime day arithmetic no longer steps on this calendar (spec/05 §2.7), so the coordinate has no shift or difference consumer here. It does not claim another model-zone missing date, checked authoring, DateTime, or target storage.
-/

namespace A12Kernel

namespace DateParts.LegacyHybrid

namespace DayCoordinate

/-- Complete Julian-calendar days before one positive-era year. -/
def daysBeforeYear (year : Int) : Int :=
  let previous := year - 1
  previous * 365 + previous.tdiv 4

/-- Complete legacy-calendar days before a month boundary. -/
def daysBeforeMonth (year : Int) (month : Nat) : Nat :=
  (List.range (month - 1)).foldl (fun total offset =>
    total + (DateParts.LegacyHybrid.daysInMonth? year (offset + 1)).getD 0) 0

/-- Zero-based Julian-calendar day coordinate from positive-era year one. -/
def julianAbsoluteDay (parts : DateParts) : Int :=
  daysBeforeYear parts.year +
    (daysBeforeMonth parts.year parts.month : Int) +
    (parts.day : Int) - 1

private def cutoverJulian : DateParts :=
  { year := 1582, month := 10, day := 4 }

private def cutoverGregorian : DateParts :=
  { year := 1582, month := 10, day := 15 }

private def cutoverGregorianEpochDay : Int :=
  CivilDate.daysBeforeYear cutoverGregorian.year +
    (CivilDate.daysBeforeMonth cutoverGregorian.year
      cutoverGregorian.month : Int) +
    (cutoverGregorian.day : Int) - 1 - 719162

end DayCoordinate

/-- Whole-day coordinate whose adjacent cutover labels are 1582-10-04 and 1582-10-15. -/
def epochDay? (parts : DateParts) : Option Int :=
  if !DateParts.LegacyHybrid.isReal parts then
    none
  else if decide (parts.Before DayCoordinate.cutoverGregorian) then
    some (DayCoordinate.cutoverGregorianEpochDay - 1 -
      (DayCoordinate.julianAbsoluteDay DayCoordinate.cutoverJulian -
      DayCoordinate.julianAbsoluteDay parts))
  else
    some (CivilDate.daysBeforeYear parts.year +
      (CivilDate.daysBeforeMonth parts.year parts.month : Int) +
      (parts.day : Int) - 1 - 719162)

/-- Resolve one real default-profile legacy Date to exact UTC midnight. This remains
    available before the stored-Date floor because the hybrid coordinate owns that era. -/
def midnightInstant? (parts : DateParts) : Option Instant :=
  (epochDay? parts).map fun epochDay =>
    { epochMillis := epochDay * 86400000 }

end DateParts.LegacyHybrid

end A12Kernel
