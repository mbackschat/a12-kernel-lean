import A12Kernel.Semantics.BerlinLegacyTimeZone
import A12Kernel.Semantics.ConstructedDateDay

/-! # Versioned model-zone capability

This capsule decodes an exact instant into its local label on the Julian–Gregorian hybrid calendar and independently resolves a label back to an instant through the selected zone profile. `Today` takes the label's date at the evaluation instant and resolves that date's midnight; the two steps stay separate because the offset at midnight can differ from the offset at the current instant. The Kernel builds its clock on a default-cutover `GregorianCalendar`, so a pinned instant before the 1582 cutover reads its Julian label (2026-10-21 letter §1.2, KF576).

Stored-value decoding through `localDateTime?` keeps the positive-era proleptic coordinate and the A12 full-Date floor, because a stored Date never lies below that floor. Other kernel-legal ids are outside these two concrete profiles.
-/

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

/-- The same date at local midnight. -/
def midnight (parts : DateParts) : LegacyCalendarLabel :=
  { parts, time := { hour := 0, minute := 0, second := 0, valid := by decide } }

end LegacyCalendarLabel

end A12Kernel

namespace A12Kernel.ModelZone

/-- The two model-zone profiles concretely implemented by this theory. This is a bounded selector, not the kernel's complete legal zone-id domain. -/
inductive ConcreteProfile where
  | utc
  | europeBerlin
  deriving Repr, DecidableEq

namespace ConcreteProfile

/-- Select one concrete profile. UTC and GMT are aliases; every other legal or illegal id remains outside this bounded capability. -/
def ofId? : String → Option ConcreteProfile
  | "UTC" | "GMT" => some .utc
  | "Europe/Berlin" => some .europeBerlin
  | _ => none

def calendarOffset? : ConcreteProfile → Instant → Option Int
  | .utc, _ => some 0
  | .europeBerlin, instant => EuropeBerlinLegacyProfile.offsetSecondsAt? instant

/-- Decode the hybrid-calendar wall label at one exact instant. Millisecond identity remains in the input instant. -/
def calendarLabel? (profile : ConcreteProfile) (instant : Instant) : Option LegacyCalendarLabel := do
  LegacyCalendarLabel.atOffset? instant (← profile.calendarOffset? instant)

def calendarOffsets : ConcreteProfile → List Int
  | .utc => [0]
  | .europeBerlin => EuropeBerlinLegacyProfile.candidateOffsets

/-- Fresh labels require an actual matching offset; the ascending candidate order retains the
legacy later-instant overlap choice. Calendar mutation has a separate gap-normalizing resolver. -/
def resolveCalendarLabel? (profile : ConcreteProfile) (label : LegacyCalendarLabel) : Option Instant := do
  let offset ← profile.calendarOffsets.find? fun offset =>
    (label.candidate? offset 0).bind profile.calendarOffset? == some offset
  label.candidate? offset 0

/-- `Today` as its hybrid-calendar date and that date's resolved midnight. The date is read at the evaluation instant's offset, the midnight under its own offset. -/
def todayLabel? (profile : ConcreteProfile) (instant : Instant) : Option (DateParts × Instant) := do
  let label ← profile.calendarLabel? instant
  pure (label.parts, ← profile.resolveCalendarLabel? (LegacyCalendarLabel.midnight label.parts))

def today? (profile : ConcreteProfile) (instant : Instant) :
    Option Instant :=
  (profile.todayLabel? instant).map (·.2)

def resolveLocal? (profile : ConcreteProfile) (dateTime : LocalDateTime) :
    Option Instant :=
  match profile with
  | .utc => some dateTime.resolveUtc
  | .europeBerlin => EuropeBerlinLegacyProfile.resolveLocal? dateTime

/-- Decode the local admitted DateTime wall label at one exact instant under this concrete profile. Millisecond identity remains in the input instant; the decoded label has the kernel's whole-second component domain. -/
def localDateTime? (profile : ConcreteProfile) (instant : Instant) :
    Option LocalDateTime :=
  match profile with
  | .utc => LocalDateTime.atOffset? instant 0
  | .europeBerlin =>
      (EuropeBerlinLegacyProfile.offsetSecondsAt? instant).bind
        (LocalDateTime.atOffset? instant)

/-- Decode the local admitted Date at one exact instant under this concrete profile. This is the rendering-side counterpart to fresh-label resolution. -/
def localDate? (profile : ConcreteProfile) (instant : Instant) :
    Option FullDate :=
  (profile.localDateTime? instant).map (·.date)

end ConcreteProfile

/-- `Today` under the model's default UTC profile. -/
def utcToday? (instant : Instant) : Option Instant :=
  ConcreteProfile.utc.today? instant

/-- `Today` under the pinned Europe/Berlin legacy profile. -/
def europeBerlinToday? (instant : Instant) : Option Instant :=
  ConcreteProfile.europeBerlin.today? instant

def concreteToday? (zoneId : String) (instant : Instant) : Option Instant :=
  (ConcreteProfile.ofId? zoneId).bind (·.today? instant)

def concreteResolveLocal? (zoneId : String) (year : Int)
    (month day hour minute second : Nat) : Option Instant := do
  let profile ← ConcreteProfile.ofId? zoneId
  let dateTime ← LocalDateTime.ofYmdHms? year month day hour minute second
  profile.resolveLocal? dateTime

def concreteRules : ModelZoneRules where
  today? := concreteToday?
  resolveLocal? := concreteResolveLocal?

end A12Kernel.ModelZone
