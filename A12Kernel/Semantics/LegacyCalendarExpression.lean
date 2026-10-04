import A12Kernel.Semantics.ModelZone
import A12Kernel.Semantics.ConstructedDateDay

namespace A12Kernel

/-- A calendar label before storage restrictions. Expression arithmetic may cross the stored-Date
floor or the four-digit year boundary (calendar-expression grid, 2026-10-04). -/
structure LegacyCalendarLabel where
  parts : DateParts
  time : TimeOfDay
  deriving Repr, DecidableEq

namespace LegacyCalendarLabel

def ofLocal (value : LocalDateTime) : LegacyCalendarLabel :=
  { parts := value.date.civil.parts, time := value.time }

def toLocal? (value : LegacyCalendarLabel) : Option LocalDateTime := do
  let date ← FullDate.ofYmd? value.parts.year value.parts.month value.parts.day
  pure { date, time := value.time }

def atOffset? (instant : Instant) (offset : Int) : Option LegacyCalendarLabel := do
  let localSecond := instant.epochMillis / 1000 + offset
  let parts ← DateParts.LegacyHybrid.ofEpochDay? (localSecond / 86400)
  let second := (localSecond % 86400).toNat
  let time ← TimeOfDay.ofHms? (second / 3600) ((second % 3600) / 60) (second % 60)
  pure { parts, time }

def candidate? (value : LegacyCalendarLabel) (offset millisecond : Int) : Option Instant := do
  let day ← DateParts.LegacyHybrid.epochDay? value.parts
  pure { epochMillis := (day * 86400 + value.time.secondsSinceMidnight - offset) * 1000 + millisecond }

end LegacyCalendarLabel

namespace ModelZone.ConcreteProfile

def calendarOffset? : ConcreteProfile → Instant → Option Int
  | .utc, _ => some 0
  | .europeBerlin, instant => EuropeBerlinLegacyProfile.offsetSecondsAt? instant

def calendarLabel? (profile : ConcreteProfile) (instant : Instant) : Option LegacyCalendarLabel := do
  LegacyCalendarLabel.atOffset? instant (← profile.calendarOffset? instant)

private def calendarOffsets : ConcreteProfile → List Int
  | .utc => [0]
  | .europeBerlin => EuropeBerlinLegacyProfile.candidateOffsets

/-- Fresh labels require an actual matching offset; the ascending candidate order retains the
legacy later-instant overlap choice. Calendar mutation has a separate gap-normalizing resolver. -/
def resolveCalendarLabel? (profile : ConcreteProfile) (label : LegacyCalendarLabel) : Option Instant := do
  let offset ← profile.calendarOffsets.find? fun offset =>
    (label.candidate? offset 0).bind profile.calendarOffset? == some offset
  label.candidate? offset 0

/-- Resolve already-classified stored components at midnight without imposing a second storage floor.
Month-only input may complete below that floor under the Base Year (fragment-limit grid, 2026-10-04). -/
def resolveCompletedDateParts? (profile : ConcreteProfile) (parts : DateParts) : Option DateValue := do
  let instant ← profile.resolveCalendarLabel? {
    parts, time := { hour := 0, minute := 0, second := 0, valid := by decide } }
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
