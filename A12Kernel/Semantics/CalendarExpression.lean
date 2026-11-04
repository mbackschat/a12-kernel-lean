import A12Kernel.Semantics.ModelZone
import A12Kernel.Semantics.ConstructedDateDay

namespace A12Kernel

namespace ModelZone.ConcreteProfile

/-- Resolve already-classified stored components at midnight without imposing a second storage floor.
Month-only input may complete below that floor under the Base Year (fragment-limit grid, 2026-10-04). -/
def resolveCompletedDateParts? (profile : ConcreteProfile) (parts : DateParts) : Option DateValue := do
  let instant ← profile.resolveCalendarLabel? (CalendarLabel.midnight parts)
  pure { instant, parts }

/-- A date constant's completed value when it is reached (spec/05 §1). The label resolves as a stored label does, so under UTC a Julian leap day the proleptic calendar lacks keeps its Julian instant, and under Europe/Berlin it has no instant at all. Date parts are those of the label decoded at the resolved instant, the day the constant actually names. -/
def resolveConstantDateParts? (profile : ConcreteProfile) (parts : DateParts) : Option DateValue := do
  let instant ← profile.resolveStoredLabel? (CalendarLabel.midnight parts)
  let label ← profile.calendarLabel? instant
  pure { instant, parts := label.parts }

private def isFebruary28 (parts : DateParts) : Bool :=
  parts.month == 2 && parts.day == 28

/-- `ZonedDateTime.plusDays`/`plusMonths`/`plusYears`: shift the label's proleptic date, keep its clock and millisecond, and resolve preferring the source offset. A year shift is a twelve-month shift, because both keep the month and clamp the day to the target month's length. -/
private def plusDate? (profile : ConcreteProfile) (unit : DateShiftUnit) (label : CalendarLabel)
    (offsetSeconds millisecond amount : Int) : Option Instant := do
  let date ← CivilDate.ofParts? label.parts
  let target ← match unit with
    | .days => date.addDays? amount
    | .months => date.addMonths? amount
    | .years => date.addMonths? (12 * amount)
  profile.resolveLabel? { label with parts := target.parts } millisecond (some offsetSeconds)

/-- Shift the calendar behind an exact instant as kernel 31.1.1 does (spec/05 §2.3). The date moves on the proleptic calendar with the clock kept, and the source offset is preferred where the target label is ambiguous. Month and year shifts add the kernel's two 28-February corrections: from a leap year's 28 February onto a common year's, the clock resets to the landing date's midnight; a year shift from a common year's 28 February onto a leap year's moves on one more day. -/
def shiftCalendar? (profile : ConcreteProfile) (unit : DateShiftUnit)
    (instant : Instant) (amount : Int) : Option (CalendarLabel × Instant) := do
  let source ← profile.calendarLabel? instant
  if amount == 0 then return (source, instant)
  let sourceOffset ← profile.calendarOffset? instant
  let millisecond := instant.epochMillis % 1000
  let shifted ← profile.plusDate? unit source sourceOffset millisecond amount
  let shiftedLabel ← profile.calendarLabel? shifted
  let sourceLeap := DateParts.isLeapYear source.parts.year
  let shiftedLeap := DateParts.isLeapYear shiftedLabel.parts.year
  let landing ←
    if unit == .days || !(isFebruary28 source.parts && isFebruary28 shiftedLabel.parts) then
      pure shifted
    else if sourceLeap && !shiftedLeap then
      profile.resolveCalendarLabel? (CalendarLabel.midnight shiftedLabel.parts)
    else if unit == .years && !sourceLeap && shiftedLeap then
      profile.plusDate? .days shiftedLabel (← profile.calendarOffset? shifted) millisecond 1
    else
      pure shifted
  pure (← profile.calendarLabel? landing, landing)

end ModelZone.ConcreteProfile
end A12Kernel
