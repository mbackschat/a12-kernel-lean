import A12Kernel.Semantics.ConstructedDateDifference
import A12Kernel.Semantics.CivilDateCoordinate

/-! # Constructed-Date legacy-hybrid day coordinate

This capsule supplies one bounded whole-day coordinate for the default October 1582 legacy-calendar cutover. Gregorian labels from 1582-10-15 onward reuse the existing civil coordinate; earlier labels use a four-year Julian cycle aligned so 1582-10-04 immediately precedes 1582-10-15. Day shift and difference then reuse the existing reason-bearing construction and numeric results.

The coordinate models the cutover profile only. It does not claim another model-zone missing date, a wall-clock instant, checked authoring, DateTime, or target storage.
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

/-- Locate a day within one four-year Julian cycle. -/
private def locateYear : Nat → Int → Nat → Option (Int × Nat)
  | 0, _, _ => none
  | fuel + 1, year, remaining =>
      let yearLength :=
        if DateParts.LegacyHybrid.isJulianLeapYear year then 366 else 365
      if remaining < yearLength then some (year, remaining)
      else locateYear fuel (year + 1) (remaining - yearLength)

/-- Locate a one-based month/day in an already selected Julian year. -/
private def locateMonth : Nat → Int → Nat → Nat → Option (Nat × Nat)
  | 0, _, _, _ => none
  | fuel + 1, year, month, remaining =>
      match DateParts.LegacyHybrid.daysInMonth? year month with
      | none => none
      | some monthLength =>
          if remaining < monthLength then some (month, remaining + 1)
          else locateMonth fuel year (month + 1) (remaining - monthLength)

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

/-- Invert the bounded legacy-hybrid day coordinate. Coordinates before positive-era year one fail closed. -/
def ofEpochDay? (epochDay : Int) : Option DateParts :=
  if DayCoordinate.cutoverGregorianEpochDay ≤ epochDay then
    (CivilDate.ofUnixEpochDay? epochDay).map (·.parts)
  else
    let absoluteDay :=
      DayCoordinate.julianAbsoluteDay DayCoordinate.cutoverJulian +
        (epochDay - (DayCoordinate.cutoverGregorianEpochDay - 1))
    if absoluteDay < 0 then
      none
    else
      let era := absoluteDay / 1461
      let dayInEra := Int.toNat (absoluteDay % 1461)
      match DayCoordinate.locateYear 4 (era * 4 + 1) dayInEra with
      | none => none
      | some (year, dayInYear) =>
          match DayCoordinate.locateMonth 12 year 1 dayInYear with
          | none => none
          | some (month, day) => some { year, month, day }

/-- Shift one real default-profile legacy label by a signed number of calendar days. -/
def addDays? (source : DateParts) (offset : Int) : Option DateParts := do
  let sourceDay ← epochDay? source
  ofEpochDay? (sourceDay + offset)

/-- Signed calendar-day steps from the first real default-profile legacy label to the second. -/
def differenceInDays? (first second : DateParts) : Option Int := do
  let firstDay ← epochDay? first
  let secondDay ← epochDay? second
  pure (secondDay - firstDay)

end DateParts.LegacyHybrid

namespace DateConstructionResult

/-- Apply a default-cutover legacy day shift while retaining every constructed no-value reason. -/
def addLegacyDays? (result : DateConstructionResult) (offset : Int) :
    Option DateConstructionResult :=
  match result with
  | .real parts => (DateParts.LegacyHybrid.addDays? parts offset).map .real
  | .incomplete => some .incomplete
  | .unreal => some .unreal
  | .unknown => some .unknown

/-- Count default-cutover legacy calendar days without collapsing unavailable, incomplete, and unreal operands. -/
def differenceLegacyDays? (first second : DateConstructionResult) :
    Option ConstructedDateNumericResult :=
  differenceWith? DateParts.LegacyHybrid.differenceInDays? first second

end DateConstructionResult

end A12Kernel
