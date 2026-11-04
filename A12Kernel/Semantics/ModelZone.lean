import A12Kernel.Semantics.BerlinLegacyTimeZone
import A12Kernel.Semantics.ConstructedDateDay

/-! # Versioned model-zone capability

This capsule decodes an exact instant into its local label on the proleptic ISO calendar and independently resolves a label back to an instant through the selected zone profile, optionally preferring one offset. `Today` takes the label's date at the evaluation instant and resolves that date's midnight; the two steps stay separate because the offset at midnight can differ from the offset at the current instant. Kernel 31.1.1 reads its clock through `java.time`, so a pinned instant before the 1582 cutover reads its proleptic label (spec/05 §2.7, §7).

Stored-value decoding through `localDateTime?` keeps the positive-era proleptic coordinate and the A12 full-Date floor, because a stored Date never lies below that floor. Other kernel-legal ids are outside these two concrete profiles.
-/

namespace A12Kernel

/-- A label real only on the hybrid calendar: a Julian leap day before the 1582 cutover in a year the proleptic calendar makes common. -/
def DateParts.isJulianOnly (parts : DateParts) : Bool :=
  DateParts.LegacyHybrid.isReal parts && !parts.isReal

/-- A proleptic calendar label before storage restrictions. Expression arithmetic may cross the stored-Date
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
  let date ← CivilDate.ofUnixEpochDay? (localSecond / 86400)
  let second := (localSecond % 86400).toNat
  let time ← TimeOfDay.ofHms? (second / 3600) ((second % 3600) / 60) (second % 60)
  pure { parts := date.parts, time }

/-- The label's wall clock in milliseconds, counted as if it were UTC; `none` when the label names no real proleptic date. -/
def wallMillis? (value : LegacyCalendarLabel) (millisecond : Int) : Option Int := do
  let date ← CivilDate.ofParts? value.parts
  pure ((date.unixEpochDay * 86400 + value.time.secondsSinceMidnight) * 1000 + millisecond)

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

/-- Decode the proleptic wall label at one exact instant. Millisecond identity remains in the input instant. -/
def calendarLabel? (profile : ConcreteProfile) (instant : Instant) : Option LegacyCalendarLabel := do
  LegacyCalendarLabel.atOffset? instant (← profile.calendarOffset? instant)

/-- Resolve a label with a millisecond remainder, preferring one offset as `ZonedDateTime.ofLocal` does: a gap label lands one gap later, an overlap label at the preferred offset when valid there and otherwise at its earlier instant (spec/05 §5). -/
def resolveLabel? (profile : ConcreteProfile) (label : LegacyCalendarLabel) (millisecond : Int)
    (preferred : Option Int) : Option Instant := do
  let wall ← label.wallMillis? millisecond
  match profile with
  | .utc => pure { epochMillis := wall }
  | .europeBerlin => EuropeBerlinLegacyProfile.resolveWall? wall preferred

/-- A fresh label at a whole second, with no preferred offset. -/
def resolveCalendarLabel? (profile : ConcreteProfile) (label : LegacyCalendarLabel) : Option Instant :=
  profile.resolveLabel? label 0 none

/-- Stored-text reality (spec/05 §4): the proleptic calendar, except that outside Europe/Berlin a Julian leap day the proleptic calendar lacks, such as 1500-02-29, is still real. Measured for UTC and Berlin only. -/
def storedLabelReal (profile : ConcreteProfile) (parts : DateParts) : Bool :=
  parts.isReal || (profile == .utc && parts.isJulianOnly)

/-- Resolve a stored or constant label (spec/05 §1, §4) as a fresh label, except that a Julian leap day the proleptic calendar lacks resolves outside Europe/Berlin to its Julian instant, ten days later on the proleptic calendar. Under Europe/Berlin that label names no instant. -/
def resolveStoredLabel? (profile : ConcreteProfile) (label : LegacyCalendarLabel) : Option Instant :=
  match profile.resolveCalendarLabel? label with
  | some instant => some instant
  | none =>
      if profile == .utc && label.parts.isJulianOnly then
        (DateParts.LegacyHybrid.epochDay? label.parts).map fun day =>
          { epochMillis := (day * 86400 + label.time.secondsSinceMidnight) * 1000 }
      else none

/-- `Today` as its calendar date and that date's resolved midnight. The date is read at the evaluation instant's offset, the midnight under its own offset. -/
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

/-- Whether the zone attains a wall label: every label under UTC, and under Berlin a label with a valid offset, so not one inside a spring gap. Resolution is injective exactly on attained labels. -/
def attains (profile : ConcreteProfile) (dateTime : LocalDateTime) : Bool :=
  match profile with
  | .utc => true
  | .europeBerlin =>
      !(EuropeBerlinLegacyProfile.validOffsets dateTime.resolveUtc.epochMillis).isEmpty

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
