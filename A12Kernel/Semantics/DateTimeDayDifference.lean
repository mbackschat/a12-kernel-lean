import A12Kernel.Semantics.DateShift
import A12Kernel.Semantics.ModelZone

/-! # Concrete model-zone calendar-day differences

This capsule implements the resolved `DifferenceInDays` core for UTC and the versioned Europe/Berlin legacy profile. Berlin makes the kernel's `365 × whole-years` lower-bound calendar landing, then counts stateful residual forward day landings in authored operand order. A gap landing uses the new offset to choose the pre-gap wall clock; an overlap landing uses the earlier instant. The adjusted wall clock then becomes the source of the next residual step.

Parsing, Date-versus-DateTime admission, empty and malformed operands, calendar identity outside the concrete profiles, numeric result storage, validation polarity, and a general model-zone interface remain separate.
-/

namespace A12Kernel.EuropeBerlinLegacyProfile

/-- Offset used by a forward calendar landing. Valid overlaps choose the larger offset and therefore the earlier instant. In a gap, the first candidate whose assumed offset exceeds the actual offset reproduces the legacy pre-gap wall clock. -/
private def forwardOffset? (dateTime : LocalDateTime) : Option Int :=
  match candidateOffsets.reverse.find? fun offsetSeconds =>
      offsetSecondsAt? (candidateInstant dateTime offsetSeconds) ==
        some offsetSeconds with
  | some offsetSeconds => some offsetSeconds
  | none =>
      candidateOffsets.find? fun offsetSeconds =>
        match offsetSecondsAt? (candidateInstant dateTime offsetSeconds) with
        | some actualOffset => actualOffset < offsetSeconds
        | none => false

/-- Resolve one nominal label created by a forward calendar addition. This deliberately differs from fresh-label resolution at gaps and overlaps. -/
private def resolveForwardLanding? (dateTime : LocalDateTime) :
    Option Instant :=
  (forwardOffset? dateTime).map (candidateInstant dateTime)

/-- Resolve and decode one policy-selected forward calendar landing. Day and year additions share this exact gap/overlap mechanism. -/
private def forwardLanding? (date : FullDate) (time : TimeOfDay) :
    Option (LocalDateTime × Instant) := do
  let nominal : LocalDateTime := { date, time }
  let landing ← resolveForwardLanding? nominal
  let actualOffset ← offsetSecondsAt? landing
  let next ← LocalDateTime.atOffset? landing actualOffset
  pure (next, landing)

/-- Add a nonnegative number of calendar days from the current resolved local state and return both the resulting local state and exact instant. -/
private def calendarDayLanding? (current : LocalDateTime)
    (currentInstant : Instant) (days : Nat) :
    Option (LocalDateTime × Instant) := do
  if days = 0 then
    pure (current, currentInstant)
  else
    let nextDate ← current.date.addDays? days
    forwardLanding? nextDate current.time

/-- Add whole years with the legacy February-28 clock reset before resolving the final calendar landing. -/
private def calendarYearLanding? (current : LocalDateTime)
    (currentInstant : Instant) (years : Nat) :
    Option (LocalDateTime × Instant) := do
  if years = 0 then
    pure (current, currentInstant)
  else
    let nextDate ← current.date.addYears? years
    let source := current.date.civil.parts
    let target := nextDate.civil.parts
    let clearClock :=
      source.month == 2 && source.day == 28 &&
        DateParts.isLeapYear source.year &&
        target.month == 2 && target.day == 28 &&
        !DateParts.isLeapYear target.year
    let time ← if clearClock then TimeOfDay.ofHms? 0 0 0 else some current.time
    forwardLanding? nextDate time

/-- Whole completed years between ordered exact instants, using the same final-landing rule as legacy calendar year addition. -/
private def wholeYears? (earlier : LocalDateTime) (earlierInstant : Instant)
    (later : LocalDateTime) (laterInstant : Instant) : Option Nat := do
  let candidate :=
    Int.toNat
      (later.date.civil.parts.year - earlier.date.civil.parts.year)
  let (_, landing) ← calendarYearLanding? earlier earlierInstant candidate
  pure (if laterInstant.epochMillis < landing.epochMillis then
    candidate - 1 else candidate)

/-- Count consecutive profile landings that do not pass the later instant. Fuel is derived from the civil-date distance; exhaustion or an unresolved landing remains explicit absence rather than collapsing to the legitimate result zero. -/
private def countResidualLandings :
    Nat → LocalDateTime → Instant → Instant → Option Int
  | 0, _, _, _ => none
  | fuel + 1, current, currentInstant, later =>
      match calendarDayLanding? current currentInstant 1 with
      | none => none
      | some (next, landing) =>
          if landing.epochMillis ≤ later.epochMillis then
            (countResidualLandings fuel next landing later).map (1 + ·)
          else
            some 0

/-- Unsigned kernel day count over ordered operands: make one `365 × whole-years` calendar jump, then count stateful residual day landings. -/
private def forwardDifferenceInDays? (earlier : LocalDateTime)
    (earlierInstant : Instant) (later : LocalDateTime)
    (laterInstant : Instant) : Option Int := do
  let years ← wholeYears? earlier earlierInstant later laterInstant
  let seedDays := years * 365
  let (seeded, seededInstant) ←
    calendarDayLanding? earlier earlierInstant seedDays
  let fuel :=
    Int.toNat
      (later.date.unixEpochDay - seeded.date.unixEpochDay) + 1
  let residual ←
    countResidualLandings fuel seeded seededInstant laterInstant
  pure (seedDays + residual)

/-- Signed stateful calendar-day count for two already resolved Berlin values. The exact instants are authoritative in overlaps; their decoded local labels drive calendar landings. -/
def differenceResolvedInDays? (first : LocalDateTime) (firstInstant : Instant)
    (second : LocalDateTime) (secondInstant : Instant) : Option Int :=
  if firstInstant.epochMillis < secondInstant.epochMillis then
    forwardDifferenceInDays? first firstInstant second secondInstant
  else if secondInstant.epochMillis < firstInstant.epochMillis then
    (forwardDifferenceInDays? second secondInstant first firstInstant).map (-·)
  else
    some 0

/-- Signed stateful calendar-day count after both fresh labels resolve under the pinned Berlin profile. -/
def differenceInDays? (first second : LocalDateTime) : Option Int := do
  let firstInstant ← resolveLocal? first
  let secondInstant ← resolveLocal? second
  differenceResolvedInDays? first firstInstant second secondInstant

end A12Kernel.EuropeBerlinLegacyProfile

namespace A12Kernel.ModelZone

/-- Signed UTC calendar-day count. With no offset transitions, this is exact whole-day truncation in authored operand order. -/
def utcDifferenceInDays (first second : LocalDateTime) : Int :=
  (second.resolveUtc.epochMillis - first.resolveUtc.epochMillis).tdiv 86400000

namespace ConcreteProfile

/-- Evaluate day difference from exact instants plus their already decoded local labels. UTC needs only instant identity; Berlin preserves the local state required by calendar stepping. -/
def differenceResolvedInDays? (profile : ConcreteProfile)
    (first : LocalDateTime) (firstInstant : Instant)
    (second : LocalDateTime) (secondInstant : Instant) : Option Int :=
  match profile with
  | .utc =>
      some ((secondInstant.epochMillis - firstInstant.epochMillis).tdiv 86400000)
  | .europeBerlin =>
      EuropeBerlinLegacyProfile.differenceResolvedInDays?
        first firstInstant second secondInstant

/-- Evaluate day difference after the caller has selected one of the concrete profiles. Fresh-label or internal profile failure remains distinct from unsupported id selection. -/
def differenceInDays? (profile : ConcreteProfile)
    (first second : LocalDateTime) : Option Int := do
  let firstInstant ← profile.resolveLocal? first
  let secondInstant ← profile.resolveLocal? second
  profile.differenceResolvedInDays? first firstInstant second secondInstant

end ConcreteProfile

/-- Compatibility String dispatch for the currently implemented model-zone profiles. Unselected ids return `none`; Berlin behavior is never extrapolated to them. -/
def concreteDifferenceInDays? (zoneId : String)
    (first second : LocalDateTime) : Option Int :=
  (ConcreteProfile.ofId? zoneId).bind
    (·.differenceInDays? first second)

end A12Kernel.ModelZone
