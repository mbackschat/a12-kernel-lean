import A12Kernel.Semantics.BaseYearDateSource
import A12Kernel.Semantics.DateShift

/-! # Date-only month/year differences

This capsule computes the signed count of completed calendar months or years over decoded date parts, then exposes that mechanism through stored/full Dates and direct or range-selected Base-Year sources. It orders the operands, tests the direct candidate period against the later date using the matching shift convention, and restores the original sign.

The shared decoded-parts mechanism does not itself accept arbitrary authored dates. Its consumers retain their own boundaries: `FullDate` preserves the stored-value floor, while configured Base Year remains floor-free. Empty or formally unavailable operands, constructed `Date(...)` legacy-hybrid identity, DateTime admission, numeric-result provenance and scale, checked field lowering, and cell effects remain outside.
-/

namespace A12Kernel

namespace DateParts

namespace Difference

/-- Linear year/month coordinate used to obtain the only two possible forward month counts. -/
def monthCoordinate (parts : DateParts) : Int :=
  parts.year * 12 + Int.ofNat parts.month - 1

/-- An admitted consumer supplies a real month; zero is an unreachable defensive default. -/
def monthLastDay (parts : DateParts) : Nat :=
  (DateParts.daysInMonth? parts.year parts.month).getD 0

/-- Completed months for an already ordered pair. The raw coordinate count is reduced only when its clamped landing passes the later day. -/
def wholeMonthsForward (earlier later : DateParts) : Int :=
  let candidate := monthCoordinate later - monthCoordinate earlier
  let landingDay :=
    DateParts.Shift.monthLandingDay earlier (monthLastDay later)
  if later.day < landingDay then candidate - 1 else candidate

/-- Completed years for an already ordered pair. The candidate landing follows `AddYears`, including last-of-February preservation. -/
def wholeYearsForward (source target : DateParts) : Int :=
  let candidate := target.year - source.year
  if source.month < target.month then
    candidate
  else if target.month < source.month then
    candidate - 1
  else
    let landingDay :=
      DateParts.Shift.yearLandingDay source (monthLastDay source)
        (monthLastDay target)
    if target.day < landingDay then candidate - 1 else candidate

/-- Restore the original operand order after evaluating a nonnegative whole-period count. Equal operands reach the reverse branch and still produce zero. -/
def signedWholePeriods
    (forward : DateParts → DateParts → Int)
    (first second : DateParts) : Int :=
  if decide (first.Before second) then forward first second
  else -(forward second first)

end Difference

end DateParts

namespace FullDate

namespace Difference

/-- Stored-Date specialization of the shared decoded-parts month counter. -/
def wholeMonthsForward (earlier later : FullDate) : Int :=
  DateParts.Difference.wholeMonthsForward earlier.civil.parts later.civil.parts

/-- Stored-Date specialization of the shared decoded-parts year counter. -/
def wholeYearsForward (earlier later : FullDate) : Int :=
  DateParts.Difference.wholeYearsForward earlier.civil.parts later.civil.parts

/-- Restore stored-Date operand order while retaining the established `FullDate` proof seam. -/
def signedWholePeriods
    (forward : FullDate → FullDate → Int)
    (first second : FullDate) : Int :=
  if first.before second then forward first second
  else -(forward second first)

end Difference

/-- Signed count of complete month shifts from the first admitted Date to the second. -/
def differenceInMonths (first second : FullDate) : Int :=
  Difference.signedWholePeriods Difference.wholeMonthsForward first second

/-- Signed count of complete year shifts from the first admitted Date to the second. -/
def differenceInYears (first second : FullDate) : Int :=
  Difference.signedWholePeriods Difference.wholeYearsForward first second

end FullDate

/-- Signed count of complete month shifts between two direct or range-selected projections of the configured Base Year. -/
def baseYearDateDifferenceInMonths (year : Int)
    (first second : BaseYearDateSource) : Int :=
  DateParts.Difference.signedWholePeriods DateParts.Difference.wholeMonthsForward
    (first.parts year) (second.parts year)

/-- Signed count of complete year shifts between two direct or range-selected projections of the configured Base Year. -/
def baseYearDateDifferenceInYears (year : Int)
    (first second : BaseYearDateSource) : Int :=
  DateParts.Difference.signedWholePeriods DateParts.Difference.wholeYearsForward
    (first.parts year) (second.parts year)

end A12Kernel
