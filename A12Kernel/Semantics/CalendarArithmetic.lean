import A12Kernel.Semantics.DateShift
import A12Kernel.Semantics.CalendarExpression

/-! # Model-zone completed-period differences

This capsule owns `DifferenceInMonths` and `DifferenceInYears` over exact instants in a concrete model-zone profile (spec/05 §2.4). The operands are ordered by instant; the year count starts from the difference of the decoded years and steps back once when the year shift from the earlier operand passes the later one; the month count starts from twelve times the year count and tests fresh month shifts from the earlier operand until one passes the later operand. Every landing is `shiftCalendar?`'s, so the 28-February corrections and the source-offset preference take part.

Parsing, Date-versus-DateTime admission, empty and malformed operands, numeric result storage and validation polarity remain with their consumers.
-/

namespace A12Kernel.ModelZone.ConcreteProfile

/-- Whole completed years between ordered exact instants. -/
def wholeYearsForward? (profile : ConcreteProfile) (earlier later : Instant) : Option Nat := do
  let earlierLabel ← profile.calendarLabel? earlier
  let laterLabel ← profile.calendarLabel? later
  let candidate := Int.toNat (laterLabel.parts.year - earlierLabel.parts.year)
  let (_, landing) ← profile.shiftCalendar? .years earlier candidate
  pure (if later.epochMillis < landing.epochMillis then candidate - 1 else candidate)

/-- Test fresh month shifts from the earlier operand until the first passes the later instant. Each candidate is shifted from the source, never from the previous landing, because chained month shifts lose a clamped day. -/
private def firstOvershootingMonth? (profile : ConcreteProfile) (source later : Instant) :
    Nat → Nat → Option Nat
  | 0, _ => none
  | fuel + 1, candidate => do
      let (_, landing) ← profile.shiftCalendar? .months source candidate
      if later.epochMillis < landing.epochMillis then
        some (candidate - 1)
      else
        firstOvershootingMonth? profile source later fuel (candidate + 1)

/-- Whole completed months between ordered exact instants. The decoded month coordinates bound the search; fuel exhaustion stays explicit. -/
def wholeMonthsForward? (profile : ConcreteProfile) (earlier later : Instant) : Option Nat := do
  let years ← profile.wholeYearsForward? earlier later
  let firstCandidate := 12 * years
  let coordinateCandidate := Int.toNat
    ((← profile.calendarLabel? later).parts.monthCoordinate -
      (← profile.calendarLabel? earlier).parts.monthCoordinate)
  let lastCandidate := max firstCandidate coordinateCandidate + 1
  profile.firstOvershootingMonth? earlier later (lastCandidate - firstCandidate + 1) firstCandidate

/-- Restore authored sign around one nonnegative completed-period count, ordering by exact instants. -/
def signedWholePeriods? (forward : Instant → Instant → Option Nat) (first second : Instant) :
    Option Int :=
  if first.epochMillis < second.epochMillis then
    (forward first second).map (fun amount => (amount : Int))
  else if second.epochMillis < first.epochMillis then
    (forward second first).map (fun amount => -(amount : Int))
  else
    some 0

/-- Signed completed months from the first exact instant to the second. -/
def differenceResolvedInMonths? (profile : ConcreteProfile) (first second : Instant) : Option Int :=
  signedWholePeriods? profile.wholeMonthsForward? first second

/-- Signed completed years from the first exact instant to the second. -/
def differenceResolvedInYears? (profile : ConcreteProfile) (first second : Instant) : Option Int :=
  signedWholePeriods? profile.wholeYearsForward? first second

end A12Kernel.ModelZone.ConcreteProfile
