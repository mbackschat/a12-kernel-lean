import A12Kernel.Semantics.DateShift

/-! # Admitted full-Date month/year differences

This capsule starts with two stored/full Dates and computes their signed count of completed calendar months or years. It orders the operands, tests the direct candidate period against the later date using the matching shift convention, and restores the original sign. Empty or formally unavailable operands, constructed `Date(...)` legacy-hybrid identity, DateTime admission, numeric-result provenance and scale, checked lowering, and cell effects remain outside.
-/

namespace A12Kernel

namespace FullDate

namespace Difference

/-- Linear year/month coordinate used to obtain the only two possible forward month counts. -/
def monthCoordinate (date : FullDate) : Int :=
  date.civil.parts.year * 12 + Int.ofNat date.civil.parts.month - 1

/-- The valid source month always supplies a length; zero is an unreachable defensive default. -/
def monthLastDay (date : FullDate) : Nat :=
  (DateParts.daysInMonth? date.civil.parts.year date.civil.parts.month).getD 0

/-- Completed months for an already ordered pair. The raw coordinate count is reduced only when its clamped landing passes the later day. -/
def wholeMonthsForward (earlier later : FullDate) : Int :=
  let candidate := monthCoordinate later - monthCoordinate earlier
  let landingDay :=
    DateParts.Shift.monthLandingDay earlier.civil.parts (monthLastDay later)
  if later.civil.parts.day < landingDay then candidate - 1 else candidate

/-- Completed years for an already ordered pair. The candidate landing follows `AddYears`, including last-of-February preservation. -/
def wholeYearsForward (earlier later : FullDate) : Int :=
  let source := earlier.civil.parts
  let target := later.civil.parts
  let candidate := target.year - source.year
  if source.month < target.month then
    candidate
  else if target.month < source.month then
    candidate - 1
  else
    let landingDay :=
      DateParts.Shift.yearLandingDay source (monthLastDay earlier)
        (monthLastDay later)
    if target.day < landingDay then candidate - 1 else candidate

/-- Restore the original operand order after evaluating a nonnegative whole-period count. Equal operands reach the reverse branch and still produce zero. -/
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

end A12Kernel
