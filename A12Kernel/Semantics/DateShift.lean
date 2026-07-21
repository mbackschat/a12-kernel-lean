import A12Kernel.Semantics.FullDate

/-! # Admitted full-Date month/year shifts

This capsule starts with a stored/full Date and an already converted integer offset. It models the post-cutover `Calendar.MONTH` day clamp and the distinct `Calendar.YEAR` end-of-February preservation, then reapplies the universal A12 Date floor. A result below that floor fails closed. Numeric truncation and 32-bit conversion, `Date(...)` legacy-hybrid provenance, partial dates, DateTime, target formatting, and result-cell effects remain outside.
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

/-- Shift an admitted Date by whole months and return the result only when it remains in the full-Date domain. -/
def addMonths? (date : FullDate) (offset : Int) : Option FullDate :=
  (date.civil.addMonths? offset).bind FullDate.ofCivil?

/-- Shift an admitted Date by whole years and return the result only when it remains in the full-Date domain. -/
def addYears? (date : FullDate) (offset : Int) : Option FullDate :=
  (date.civil.addYears? offset).bind FullDate.ofCivil?

end FullDate

end A12Kernel
