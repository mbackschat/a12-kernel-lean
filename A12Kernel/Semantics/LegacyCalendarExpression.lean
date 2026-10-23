import A12Kernel.Semantics.ModelZone
import A12Kernel.Semantics.ConstructedDateDay

namespace A12Kernel

namespace ModelZone.ConcreteProfile

/-- Resolve already-classified stored components at midnight without imposing a second storage floor.
Month-only input may complete below that floor under the Base Year (fragment-limit grid, 2026-10-04). -/
def resolveCompletedDateParts? (profile : ConcreteProfile) (parts : DateParts) : Option DateValue := do
  let instant ← profile.resolveCalendarLabel? (LegacyCalendarLabel.midnight parts)
  pure { instant, parts, basis := .storedGregorian }

private def calendarComputeTime? (profile : ConcreteProfile) (label : LegacyCalendarLabel)
    (millisecond : Int) : Option Instant := do
  let actualOffset (offset : Int) := (label.candidate? offset millisecond).bind profile.calendarOffset?
  let offset ← (profile.calendarOffsets.find? fun offset => actualOffset offset == some offset).orElse fun _ =>
    profile.calendarOffsets.reverse.find? fun offset => (actualOffset offset).any (offset < ·)
  label.candidate? offset millisecond

/-- Mutate the calendar behind an exact instant. Day shifts retain the source offset and refit only
within the selected date; month/year shifts use compute-time resolution and the February clock reset.
The basis is spec/05 calendar arithmetic and the retained Berlin discontinuity matrices. -/
def shiftCalendar? (profile : ConcreteProfile) (unit : DateShiftUnit)
    (instant : Instant) (offset : Int) : Option (LegacyCalendarLabel × Instant) := do
  let source ← profile.calendarLabel? instant
  if offset == 0 then return (source, instant)
  let parts ← match unit with
    | .days => DateParts.LegacyHybrid.addDays? source.parts offset
    | .months => DateParts.LegacyHybrid.addMonths? source.parts offset
    | .years => DateParts.LegacyHybrid.addYears? source.parts offset
  let clearClock := unit != .days && source.parts.month == 2 && source.parts.day == 28 &&
    DateParts.isLeapYear source.parts.year && parts.month == 2 && parts.day == 28 &&
    !DateParts.isLeapYear parts.year
  let time := if clearClock then ({ hour := 0, minute := 0, second := 0, valid := by decide } : TimeOfDay) else source.time
  let millisecond := if clearClock then 0 else instant.epochMillis % 1000
  let nominal : LegacyCalendarLabel := { parts, time }
  let landing ← match unit with
    | .months | .years => profile.calendarComputeTime? nominal millisecond
    | .days => do
        let sourceOffset ← profile.calendarOffset? instant
        let first ← nominal.candidate? sourceOffset millisecond
        let actualOffset ← profile.calendarOffset? first
        if actualOffset == sourceOffset then pure first else do
          let refitted ← nominal.candidate? actualOffset millisecond
          let label ← profile.calendarLabel? refitted
          pure (if label.parts == parts then refitted else first)
  pure (← profile.calendarLabel? landing, landing)

end ModelZone.ConcreteProfile
end A12Kernel
