import A12Kernel.Semantics.CivilDateCoordinate

/-! # Admitted full-Date day/month/year shifts

This capsule starts with a stored/full Date and an already converted integer offset. Day shifting uses a bounded inverse of the existing Gregorian day coordinate; month shifting applies the post-cutover target-day clamp; year shifting applies the distinct end-of-February preservation. Every result passes through the universal A12 Date floor. Numeric truncation and 32-bit conversion, `Date(...)` legacy-hybrid provenance, partial dates, DateTime, target formatting, and result-cell effects remain outside.
-/

namespace A12Kernel

namespace DateParts

namespace Shift

/-- Day selected by a month shift once the target month's length is known. -/
def monthLandingDay (source : DateParts) (targetLastDay : Nat) : Nat :=
  min source.day targetLastDay

/-- Day selected by a year shift once both February-sensitive month lengths are known. -/
def yearLandingDay (source : DateParts) (sourceLastDay targetLastDay : Nat) : Nat :=
  let sourceIsFebruaryEnd :=
    source.month == 2 && source.day == sourceLastDay
  if sourceIsFebruaryEnd then targetLastDay
  else monthLandingDay source targetLastDay

end Shift

/-- Shift a positive-era Gregorian year/month pair by an integer number of months using Euclidean division. Calendar reality remains the following constructor's responsibility. -/
private def shiftedYearMonth (parts : DateParts) (offset : Int) : Int × Nat :=
  let totalMonths := parts.year * 12 + Int.ofNat parts.month - 1 + offset
  (totalMonths / 12, Int.toNat (totalMonths % 12) + 1)

end DateParts

namespace CivilDate

/-- Gregorian month shift with target-month day clamping. -/
private def addMonths? (date : CivilDate) (offset : Int) : Option CivilDate :=
  let (targetYear, targetMonth) := date.parts.shiftedYearMonth offset
  match DateParts.daysInMonth? targetYear targetMonth with
  | none => none
  | some targetLastDay =>
      CivilDate.ofYmd? targetYear targetMonth
        (DateParts.Shift.monthLandingDay date.parts targetLastDay)

/-- Gregorian year shift with the kernel's distinct last-of-February preservation. Other days merely clamp to the target month's length. -/
private def addYears? (date : CivilDate) (offset : Int) : Option CivilDate :=
  let targetYear := date.parts.year + offset
  match
      DateParts.daysInMonth? date.parts.year date.parts.month,
      DateParts.daysInMonth? targetYear date.parts.month with
  | some sourceLastDay, some targetLastDay =>
      CivilDate.ofYmd? targetYear date.parts.month
        (DateParts.Shift.yearLandingDay date.parts sourceLastDay targetLastDay)
  | _, _ => none

end CivilDate

namespace FullDate

/-- Shift an admitted Date by whole days in work bounded independently of the offset, then reapply the full-Date floor. -/
def addDays? (date : FullDate) (offset : Int) : Option FullDate :=
  if offset = 0 then
    some date
  else
    (CivilDate.ofUnixEpochDay? (date.unixEpochDay + offset)).bind
      FullDate.ofCivil?

/-- Shift an admitted Date by whole months and return the result only when it remains in the full-Date domain. -/
def addMonths? (date : FullDate) (offset : Int) : Option FullDate :=
  (date.civil.addMonths? offset).bind FullDate.ofCivil?

/-- Shift an admitted Date by whole years and return the result only when it remains in the full-Date domain. -/
def addYears? (date : FullDate) (offset : Int) : Option FullDate :=
  (date.civil.addYears? offset).bind FullDate.ofCivil?

end FullDate

end A12Kernel
